/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
-/
import Mathlib
import ExtremeValueProject.AffineTransformation

section cauchy_hamel_functional_equation

open Real Set Pointwise MeasureTheory

lemma eq_iUnion_connectedComponentIn (U : Set ℝ) :
    U = ⋃ x ∈ U, connectedComponentIn U x := by
  apply subset_antisymm
  · intro x x_in_U
    simpa using ⟨x, x_in_U, mem_connectedComponentIn x_in_U⟩
  · simp only [iUnion_subset_iff]
    intro x x_in_U
    exact connectedComponentIn_subset U x

lemma eq_sUnion_connectedComponentIn (U : Set ℝ) :
    U = ⋃₀ {C | ∃ x ∈ U, C = connectedComponentIn U x} := by
  apply subset_antisymm
  · intro x x_in_U
    simpa using ⟨x, x_in_U, mem_connectedComponentIn x_in_U⟩
  · simp only [sUnion_subset_iff, mem_setOf_eq, forall_exists_index, and_imp]
    intro C x x_in_U hC
    simpa [hC] using connectedComponentIn_subset U x

-- TODO: This seems to be missing in Mathlib. Compare with `connectedComponent_disjoint`.
lemma connectedComponentIn_disjoint {α : Type*} [TopologicalSpace α] {s : Set α} {x y : α}
    (h : connectedComponentIn s x ≠ connectedComponentIn s y) :
    Disjoint (connectedComponentIn s x) (connectedComponentIn s y) :=
  Set.disjoint_left.2 fun _ hzx hzy ↦
    h <| (connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm

-- TODO: Maybe not really needed; we have `connectedComponentIn_disjoint`.
lemma pairwise_disjoint_connectedComponentIn (U : Set ℝ) :
    {C | ∃ x ∈ U, C = connectedComponentIn U x}.Pairwise Disjoint := by
  intro C hC D hD hCD
  obtain ⟨x, x_in_U, C_eq⟩ := hC
  obtain ⟨y, y_in_U, D_eq⟩ := hD
  rw [C_eq, D_eq] at hCD ⊢
  exact connectedComponentIn_disjoint hCD

-- TODO: Is this missing from Mathlib?
lemma IsOpen.isOpen_connectedComponentIn {α : Type*} [TopologicalSpace α]
    {s : Set α} (s_loc_conn : LocallyConnectedSpace s) (s_open : IsOpen s) {x : α} :
    IsOpen (connectedComponentIn s x) := by
  by_cases hxs : x ∉ s
  · simp [connectedComponentIn, hxs]
  rw [not_not] at hxs
  simp only [connectedComponentIn, hxs, ↓reduceDIte]
  obtain ⟨U, U_open, hU⟩ := @isOpen_connectedComponent s _ s_loc_conn ⟨x, hxs⟩
  have obs : Subtype.val '' connectedComponent ⟨x, hxs⟩ = U ∩ s := by
    ext y
    simp only [mem_image, Subtype.exists, exists_and_right, exists_eq_right, mem_inter_iff]
    refine ⟨?_, ?_⟩
    · intro ⟨y_in_s, hy⟩
      exact ⟨by simpa [← hU] using hy, y_in_s⟩
    · intro ⟨y_in_U, y_in_s⟩
      exact ⟨y_in_s, by simpa [← hU] using y_in_U⟩
  simpa [obs] using U_open.inter s_open

private lemma TopologicalSpace.SeparableSpace.countable_of_disjoint_of_isOpen_of_nonempty
    {α : Type*} [TopologicalSpace α] (sep : SeparableSpace α) {As : Set (Set α)}
    (As_disj : As.Pairwise Disjoint) (As_open : ∀ A ∈ As, IsOpen A)
    (As_nonemp : ∀ A ∈ As, A.Nonempty)  :
    As.Countable := by
  obtain ⟨s, s_ctble, s_dense⟩ := sep.exists_countable_dense
  have aux (A) (hA : A ∈ As) : ∃ x ∈ s, x ∈ A :=
    s_dense.exists_mem_open (As_open A hA) (As_nonemp A hA)
  set g : As → s := fun A ↦ ⟨(aux A.val A.prop).choose, (aux A.val A.prop).choose_spec.1⟩ with def_g
  have hg (A : As) : (g A).val ∈ A.val := (aux A.val A.prop).choose_spec.2
  have g_inj : Function.Injective g := by
    intro A B hAB
    by_contra maybe_ne
    apply (As_disj A.prop B.prop (Subtype.coe_ne_coe.mpr maybe_ne)).notMem_of_mem_left (hg A)
    simpa [← hAB] using (hg B)
  rw [Set.countable_iff_exists_injective] at s_ctble ⊢
  obtain ⟨f, f_inj⟩ := s_ctble
  refine ⟨f ∘ g, f_inj.comp g_inj⟩

-- TODO: Is this missing from Mathlib?
lemma TopologicalSpace.SeparableSpace.countable_of_disjoint_of_isOpen
    {α : Type*} [TopologicalSpace α] (sep : SeparableSpace α) {As : Set (Set α)}
    (As_disj : As.Pairwise Disjoint) (As_open : ∀ A ∈ As, IsOpen A) :
    As.Countable := by
  suffices (As \ {∅}).Countable from
    Countable.mono (show As ⊆ (As \ {∅}) ∪ {∅} by simp) (this.union (countable_singleton ∅))
  apply countable_of_disjoint_of_isOpen_of_nonempty sep
  · exact As_disj.mono sdiff_subset
  · exact fun A hA ↦ As_open A (mem_of_mem_sdiff hA)
  · intro A hA
    simp only [mem_sdiff, mem_singleton_iff] at hA
    exact nonempty_iff_ne_empty.mpr hA.2

lemma ConnectedComponents.mk_eq_mk_iff {α : Type*} [TopologicalSpace α] {x y : α} :
    ConnectedComponents.mk x = ConnectedComponents.mk y
      ↔ connectedComponent x = connectedComponent y := by
  simp_all only [coe_eq_coe]

lemma ConnectedComponents.mk_out_eq {α : Type*} [TopologicalSpace α] (C : ConnectedComponents α) :
    ConnectedComponents.mk (Quot.out C) = C :=
  Quotient.out_eq _

--lemma ConnectedComponents.out_mem_connectedComponent {α : Type*} [TopologicalSpace α] (C : ConnectedComponents α) :
--    (Quot.out C) ∈ connectedComponent (Quot.out C) := by
--  exact mem_connectedComponent

lemma TopologicalSpace.SeparableSpace.countable_connectedComponents {α : Type*} [TopologicalSpace α]
    [LocallyConnectedSpace α] (sep : SeparableSpace α) :
    Countable (ConnectedComponents α) := by
  set φ : ConnectedComponents α → Set α := (fun A ↦ connectedComponent (Quot.out A)) with def_φ
  set As : Set (Set α) := Set.range φ with def_As
  have key := @countable_of_disjoint_of_isOpen α _ sep As ?_ ?_
  · obtain ⟨f, f_inj⟩ := Set.countable_iff_exists_injective.mp key
    apply (countable_iff_exists_injective _).mpr ⟨fun C ↦ f (rangeFactorization φ C), f_inj.comp ?_⟩
    intro C₁ C₂ hC
    simp only [rangeFactorization, Subtype.mk.injEq, φ, As] at hC
    exact Quotient.out_equiv_out.mp hC
  · intro A₁ hA₁ A₂ hA₂ hA_ne
    simp only [mem_range, As, φ] at hA₁ hA₂
    obtain ⟨C₁, hC₁⟩ := hA₁
    obtain ⟨C₂, hC₂⟩ := hA₂
    rw [← hC₁, ← hC₂] at hA_ne ⊢
    exact connectedComponent_disjoint hA_ne
  · intro A hA
    simp only [def_As, mem_range, As, φ] at hA
    obtain ⟨C, hAC⟩ := hA
    simpa [← hAC] using isOpen_connectedComponent

-- TODO: Missing from Mathlib?
open TopologicalSpace in
lemma IsOpen.separableSpace {α : Type*} [TopologicalSpace α] [SeparableSpace α]
    {s : Set α} (s_open : IsOpen s) :
    SeparableSpace s := by
  obtain ⟨c, c_ctble, c_dense⟩ := ‹SeparableSpace α›.exists_countable_dense
  refine ⟨⟨(↑) ⁻¹' c, c_ctble.preimage Subtype.val_injective, ?_⟩⟩
  simpa [Subtype.dense_iff] using c_dense.open_subset_closure_inter s_open

open TopologicalSpace in
lemma IsOpen.countable_setOf_connectedComponentIn
    {α : Type*} [TopologicalSpace α] [LocallyConnectedSpace α] [sep : SeparableSpace α]
    {s : Set α} (s_open : IsOpen s) :
    Countable {C : Set α | ∃ x ∈ s, C = connectedComponentIn s x} := by
  have : LocallyConnectedSpace s := s_open.locallyConnectedSpace
  have sep_s : SeparableSpace s := s_open.separableSpace
  have key := SeparableSpace.countable_connectedComponents (α := s) inferInstance
  let ψ : {C : Set α | ∃ x ∈ s, C = connectedComponentIn s x} → ConnectedComponents s :=
    fun C ↦ ConnectedComponents.mk
            ⟨(mem_setOf_eq.mp C.prop).choose, (mem_setOf_eq.mp C.prop).choose_spec.1⟩
  have ψ_inj : Function.Injective ψ := by
    intro C₁ C₂ hψC
    ext1
    have aux₁ := (mem_setOf_eq.mp C₁.prop).choose_spec
    have aux₂ := (mem_setOf_eq.mp C₂.prop).choose_spec
    rw [aux₁.2, aux₂.2]
    simp only [ψ, ConnectedComponents.coe_eq_coe] at hψC
    rw [connectedComponentIn_eq_image aux₁.1, connectedComponentIn_eq_image aux₂.1]
    exact congr_arg (Subtype.val '' ·) hψC
  exact Function.Injective.countable ψ_inj

-- TODO: Hopefully this is not needed and `Real.convex_iff_isPreconnected` is enough.
lemma Real.eq_Ioo_or_Iio_or_Ioi_or_univ_of_isOpen_of_isConnected
    {U : Set ℝ} (U_open : IsOpen U) (U_conn : IsConnected U) :
    (∃ a b, U = Ioo a b) ∨ (∃ b, U = Iio b) ∨ (∃ a, U = Ioi a) ∨ U = univ := by
  sorry

lemma Real.eq_Ioo_of_isOpen_of_isConnected_of_isFinite
    {U : Set ℝ} (U_open : IsOpen U) (U_conn : IsConnected U) (U_fin : volume U < ⊤) :
    ∃ a b : ℝ, U = Ioo a b := by
  sorry

lemma exists_interval_measure_inter_gt_mul_measure
    {A : Set ℝ} (A_mble : MeasurableSet A) (A_pos : 0 < volume A) (A_fin : volume A < ⊤)
    {r : ℝ} (one_lt_r : 1 < r) :
    ∃ (J : Set ℝ), IsConnected J ∧ (interior J).Nonempty ∧
                   volume J < (ENNReal.ofReal r) * volume (A ∩ J) := by
  let er := ENNReal.ofReal r
  have A_ne_top : volume A ≠ ⊤ := LT.lt.ne_top A_fin
  have r_mul_A_ne_top : er * volume A ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (LT.lt.ne_top A_fin)
  have A_lt_r_mul_A : volume A < er * volume A := by
       rw (occs := .pos [1]) [← one_mul (volume A)]
       apply ENNReal.mul_lt_mul_left <;> aesop
  obtain ⟨U, U_superset_A, U_open, U_lt_r_mul_A⟩ :=
    exists_isOpen_lt_of_lt (μ := volume) A (er * (volume A)) A_lt_r_mul_A
  let comps := {C : Set ℝ | ∃ x ∈ U, C = connectedComponentIn U x}
  have comps_countable : Countable comps :=
    IsOpen.countable_setOf_connectedComponentIn U_open
  have comps_disjoint : comps.Pairwise Disjoint := pairwise_disjoint_connectedComponentIn U
  have comps_disjoint' :
      Pairwise (Function.onFun Disjoint fun (i : { c // c ∈ comps }) ↦ (fun x ↦ A ∩ x) i) := by
    intro i j hij
    suffices i_j_disjoint : Disjoint (i : Set ℝ) (j : Set ℝ)
      from Disjoint.inter_right' A (Disjoint.inter_left' A i_j_disjoint)
    exact comps_disjoint i.prop j.prop (Subtype.coe_ne_coe.mpr hij)
  have comps_open (c : Set ℝ) (c_in_comps : c ∈ comps) : IsOpen c := by
    obtain ⟨_, _, c_is_comp⟩ := c_in_comps
    simpa [c_is_comp] using IsOpen.connectedComponentIn U_open
  have union_S_eq_U : ⋃ (i : { c : Set ℝ // c ∈ comps}), i.val = U := by
    rw [← Set.sUnion_eq_iUnion, eq_sUnion_connectedComponentIn U]
  have ex_comp_with_prop : ∃ c ∈ comps, volume c < er * volume (A ∩ c) := by
    by_contra hc
    have hc : ∀ c ∈ comps, er * volume (A ∩ c) ≤ volume c := by simpa using hc
    have contradiction : er * volume A ≤ volume U := calc
      er * volume A
      _ = er * volume (A ∩ U) := by rw [← left_eq_inter.mpr U_superset_A]
      _ = er * volume (A ∩ ⋃ (i : { c : Set ℝ // c ∈ comps }), i.val) := by rw [union_S_eq_U]
      _ = er * volume (⋃ (i : { c : Set ℝ // c ∈ comps }), A ∩ i.val) := by rw [inter_iUnion]
      _ = er * ∑' (i : { c // c ∈ comps }), volume (A ∩ i.val)        := by
        have h :
          volume (⋃ (i : { c // c ∈ comps}), (A ∩ ·) i) =
            ∑' (i : {c // c∈ comps }), volume ((A ∩ ·) i) :=
          measure_iUnion
            comps_disjoint'
            fun c ↦ MeasurableSet.inter A_mble (IsOpen.measurableSet (comps_open c c.prop))
        rw [h]
      _ = ∑' (i : { c // c ∈ comps }), er * volume (A ∩ i.val) := by rw [ENNReal.tsum_mul_left]
      _ ≤ ∑' (i : { c // c ∈ comps }), volume i.val  := by grw [hc]; exact Subtype.coe_prop i
      _ = volume (⋃ (i : { c // c ∈ comps }), i.val) := by
        exact (measure_iUnion
          ((pairwise_subtype_iff_pairwise_set comps Disjoint).mpr comps_disjoint)
          (fun c ↦ MeasurableSpace.measurableSet_generateFrom (comps_open c.val c.prop))).symm
      _ = volume U := by rw [union_S_eq_U]
    exact (not_lt_of_ge contradiction) U_lt_r_mul_A
  obtain ⟨c, c_in_comps, c_lt_r_mul_A_inter_c⟩ := ex_comp_with_prop
  have c_open : IsOpen c := comps_open c c_in_comps
  obtain ⟨_, _, c_is_comp⟩ := c_in_comps
  have c_pos : 0 < (volume c).toReal := by
    apply ENNReal.toReal_pos
    · apply IsOpen.measure_ne_zero volume c_open
      rwa [c_is_comp, connectedComponentIn_nonempty_iff]
    · suffices volume c < ⊤ from LT.lt.ne_top c_lt_r_mul_A_inter_c
      calc
            volume c
        _ < er * volume (A ∩ c) := gt_iff_lt.mp c_lt_r_mul_A_inter_c
        _ ≤ er * volume A       := by grw [measure_mono inter_subset_left]
        _ < ⊤                  := Ne.lt_top' (id (Ne.symm r_mul_A_ne_top))
  have c_nonempty : c.Nonempty :=
    (IsOpen.measure_pos_iff (μ := volume) c_open).mp
      ((ENNReal.toReal_lt_toReal ENNReal.zero_ne_top (LT.lt.ne_top c_lt_r_mul_A_inter_c)).mp
        c_pos)
  refine ⟨c, ?_, ?_, ?_⟩
  · rwa [c_is_comp, isConnected_connectedComponentIn_iff]
  · simpa [IsOpen.interior_eq c_open] using c_nonempty
  · exact c_lt_r_mul_A_inter_c

lemma exists_subinterval_preserving_volume_property
    {A : Set ℝ} {a b : ℝ} (a_le_b : a < b) {r : ENNReal}
    (h : volume (Ioo a b) < r * volume (A ∩ Ioo a b))
    {m : ℕ} (m_pos : 0 < m) :
    ∃ i : Fin m,
               volume (Ioo (a + (b - a) * (i / m)) (a + (b - a) * ((i + 1) / m))) <
      r * volume (A ∩ (Ioo (a + (b - a) * (i / m)) (a + (b - a) * ((i + 1) / m)))) := by
  let j₀ (i : ℕ) := a + (b - a) * (i / m)
  let j₁ (i : ℕ) := a + (b - a) * ((i + 1) / m)
  have j₁_eq_j₀_comp_add_one : j₁ = j₀ ∘ (· + 1) := by
    ext i
    unfold j₁
    exact_mod_cast rfl
  have j₀_mono : StrictMono j₀ := by
    intro i j i_lt_j
    unfold j₀
    apply add_lt_add_right
    apply (mul_lt_mul_iff_right₀ (show 0 < b - a by positivity)).mpr
    apply (div_lt_div_iff_of_pos_right (by exact_mod_cast m_pos)).mpr
    exact_mod_cast i_lt_j
  have j₁_mono : StrictMono j₁ := by
    rw [j₁_eq_j₀_comp_add_one]
    exact StrictMono.comp j₀_mono add_left_strictMono
  let J (i : ℕ) := Ioo (j₀ i) (j₁ i)
  have Ji_sub_Ioo (i : Fin m) : (J i) ⊆ Ioo a b := by
    by_cases i_ne_zero : (i : ℕ) = 0
    · rw [i_ne_zero]
      unfold J j₀ j₁
      simp [zero_div]
      apply Ioo_subset_Ioo
      · rfl
      · grw [Nat.cast_inv_le_one m]
        linarith
        positivity
    intro x hx
    unfold J j₀ j₁ at hx
    rw [Set.mem_Ioo] at hx ⊢
    obtain ⟨l, r⟩ := hx
    have : 0 < (b - a) * (i / m) := by positivity
    have aux : (b - a) * ((i + 1) / m) ≤ (b - a) := by
      rw (occs := .pos [2]) [← mul_one (b - a)]
      apply mul_le_mul_of_nonneg_left
      · rw [div_le_one]
        · suffices i_lt_m : i < m by exact_mod_cast i_lt_m
          exact_mod_cast i.prop
        · positivity
      · positivity
    have : a < a + (b - a) * (i / m) := by linarith
    have : a + (b - a) * ((i + 1) / m) ≤ b := by linarith
    constructor <;> linarith
  have interval_sdiff_subintervals_eq_endpoints (m : ℕ) :
      Ioo (j₀ 0) (j₁ m) \ ⋃ i : Fin (m + 1), Ioo (j₀ i) (j₁ i)
      = ⋃ i : Fin m, {j₁ i} := by
    induction m with
    | zero =>
        unfold j₀ j₁
        simp
        rw [Set.sdiff_eq_empty, Set.iUnion_const]
    | succ m ih =>
        have some_id (a b c : ℝ) (hab : a < b) (hbc : b < c) :
            Ioo a c = Ioc a b ∪ Ioo b c := by
          apply Subset.antisymm
          · exact Set.Ioo_subset_Ioc_union_Ioo
          · intro x hx
            rw [Set.mem_Ioo]
            match hx with
            | Or.inl hx =>
              rw [Set.mem_Ioc] at hx
              obtain ⟨_, _⟩ := hx
              constructor <;> linarith
            | Or.inr hx =>
              rw [Set.mem_Ioo] at hx
              obtain ⟨_, _⟩ := hx
              constructor <;> linarith
        have : Ioo (j₀ 0) (j₁ m) ∪ Ioo (j₁ m) (j₁ (m + 1))
             = Ioo (j₀ 0) (j₁ (m + 1)) \ {j₁ m} := by
          have (a b c : ℝ) (hab : a < b) (hbc : b < c) :
            Ioo a b ∪ Ioo b c = Ioo a c \ {b} := by grind
          apply this
          · rw [j₁_eq_j₀_comp_add_one]
            dsimp
            apply StrictMono.imp j₀_mono
            exact Nat.zero_lt_succ m
          · apply StrictMono.imp j₁_mono
            norm_num
        have j₀0_lt_j₁m : j₀ 0 < j₁ m := by
          rw [j₁_eq_j₀_comp_add_one]
          dsimp
          apply j₀_mono
          exact Nat.zero_lt_succ m
        calc
              Ioo (j₀ 0) (j₁ (m + 1)) \ ⋃ i : Fin (m + 1 + 1), Ioo (j₀ i) (j₁ i)
          _ = (Ioc (j₀ 0) (j₁ m) ∪ Ioo (j₁ m) (j₁ (m + 1)) ) \
                ⋃ i : Fin (m + 1 + 1), Ioo (j₀ i) (j₁ i) := by
            rw [some_id]
            · exact j₀0_lt_j₁m
            · exact j₁_mono (lt_add_one m)
          _ = (Ioc (j₀ 0) (j₁ m) ∪ Ioo (j₁ m) (j₁ (m + 1)) ) \
                (Ioo (j₁ m) (j₁ (m + 1)) ∪ ⋃ i : Fin (m + 1), Ioo (j₀ i) (j₁ i)) := by
            suffices ⋃ i : Fin (m + 1 + 1), Ioo (j₀ ↑i) (j₁ ↑i)
                     = Ioo (j₁ m) (j₁ (m + 1)) ∪ ⋃ i : Fin (m + 1), Ioo (j₀ ↑i) (j₁ ↑i)
              by rw [this]
            rw [Set.iUnion_fin_add_one_eq_iUnion_castSucc]
            show (⋃ i : Fin (m + 1), Ioo (j₀ i.castSucc) (j₁ i.castSucc))
                   ∪ Ioo (j₀ (Fin.last (m + 1))) (j₁ (Fin.last (m + 1)))
                 = Ioo (j₁ m) (j₁ (m + 1)) ∪ ⋃ i : Fin (m + 1), Ioo (j₀ ↑i) (j₁ ↑i)
            have h₁ : Ioo (j₀ (Fin.last (m + 1))) (j₁ (Fin.last (m + 1)))
                      = Ioo (j₁ m) (j₁ (m + 1)) := by
              rw [Fin.val_last, j₁_eq_j₀_comp_add_one]
              dsimp
            have h₂ : (⋃ i : Fin (m + 1), Ioo (j₀ i.castSucc) (j₁ i.castSucc))
                      = ⋃ i : Fin (m + 1), Ioo (j₀ ↑i) (j₁ ↑i) := by
              exact iUnion_congr (congrFun rfl)
            rw [union_comm, h₁, h₂]
          _ = (Ioc (j₀ 0) (j₁ m)) \ ⋃ i : Fin (m + 1), Ioo (j₀ i) (j₁ i) := by
            rw [union_sdiff_distrib]
            have : (Ioo (j₁ m) (j₁ (m + 1))
                     \ (Ioo (j₁ m) (j₁ (m + 1)) ∪ ⋃ i : Fin (m + 1), Ioo (j₀ ↑i) (j₁ ↑i))) = ∅ := by
              rw [Set.sdiff_eq_empty]
              exact subset_union_left
            rw [this, union_empty]
            have : Ioc (j₀ 0) (j₁ m) ∩ Ioo (j₁ m) (j₁ (m + 1)) ⊆ ∅ := by
              intro x hx
              obtain ⟨x_in_Ioc, x_in_Ioo⟩ := hx
              rw [Set.mem_Ioc] at x_in_Ioc
              rw [Set.mem_Ioo] at x_in_Ioo
              linarith
            have : Disjoint (Ioc (j₀ 0) (j₁ m)) (Ioo (j₁ m) (j₁ (m + 1))) := by
              apply Set.disjoint_iff_inter_eq_empty.mpr
              ext x; constructor <;> intro hx
              · exact this hx
              · exact not_notMem.mp fun a => hx
            rw [← Set.sdiff_sdiff, sdiff_eq_left.mpr this]
          _ = ((Ioo (j₀ 0) (j₁ m) ∪ {j₁ m}) \
                ⋃ i : Fin (m + 1), Ioo (j₀ i) (j₁ i)) := by
            suffices Ioc (j₀ 0) (j₁ m) = Ioo (j₀ 0) (j₁ m) ∪ {j₁ m} by rw [this]
            exact (Set.Ioo_union_right j₀0_lt_j₁m).symm
          _ = ((Ioo (j₀ 0) (j₁ m)) \
                ⋃ i : Fin (m + 1), Ioo (j₀ i) (j₁ i)) ∪ {j₁ m} := by
            suffices j₁m_disj : Disjoint {j₁ m} (⋃ i : Fin (m + 1), Ioo (j₀ i) (j₁ i)) by
              rw [Set.union_sdiff_distrib, sdiff_eq_left.mpr j₁m_disj]
            apply Set.disjoint_iff_inter_eq_empty.mpr
            apply Set.eq_empty_of_subset_empty
            intro x hx
            obtain ⟨x_in_j₁m, x_in_iUnion⟩ := hx
            have : x < j₁ m := by
              obtain ⟨i, x_in_Ioo⟩ := Set.mem_iUnion.mp x_in_iUnion
              rw [Set.mem_Ioo] at x_in_Ioo
              suffices ji_le_jm : j₁ i ≤ j₁ m from Std.lt_of_lt_of_le x_in_Ioo.right ji_le_jm
              apply j₁_mono.monotone
              exact Fin.is_le i
            have : x = j₁ m := by
              exact ext_cauchy (congrArg cauchy x_in_j₁m)
            linarith
          _ = (⋃ i : Fin m, {j₁ i}) ∪ {j₁ m} := by rw [ih]
          _ = ⋃ i : Fin (m + 1), {j₁ i} := by
            rw [Set.iUnion_fin_add_one_eq_iUnion_castSucc]
            show (⋃ i : Fin m, {j₁ i}) ∪ {j₁ m}
                 = (⋃ i : Fin m, {j₁ i.castSucc}) ∪ {j₁ (Fin.last m)}
            have hl : ⋃ i : Fin m, {j₁ i} = (⋃ i : Fin m, {j₁ i.castSucc}) := by
              exact iUnion_congr (congrFun rfl)
            have hr : ({j₁ m} : Set ℝ) = {j₁ (Fin.last (m))} := by
              rw [Fin.val_last]
            rw [hl, hr]
  have J_disj : Pairwise (Function.onFun Disjoint fun i : Fin m ↦ J i) := by
    intro i j i_ne_j
    unfold Function.onFun
    rw [Set.Ioo_disjoint_Ioo]
    rw [← Monotone.map_min j₁_mono.monotone]
    rw [← Monotone.map_max j₀_mono.monotone]
    have : (min i j : ℕ) + 1 ≤ max i j := by
      have : (min i j : ℕ) < max i j := by
        exact_mod_cast inf_lt_sup.mpr i_ne_j
      exact Order.add_one_le_iff.mpr this
    show j₁ (min i j) ≤ j₀ (max i j)
    unfold j₁
    exact_mod_cast Monotone.imp j₀_mono.monotone this
  have interval_eq_subintervals : volume (A ∩ ⋃ (i : Fin m), J i) = volume (A ∩ Ioo a b) := by
    apply MeasureTheory.measure_eq_measure_of_null_sdiff
    · apply Set.inter_subset_inter_right
      exact iUnion_subset Ji_sub_Ioo
    · suffices no_A : volume (Ioo a b \ (⋃ i : Fin m, J i)) = 0 by
        have subs : (A ∩ Ioo a b) \ (A ∩ ⋃ i : Fin m, J i) ⊆ Ioo a b \ (⋃ i : Fin m, J i) := by
          rw [← Set.inter_sdiff_distrib_left]
          exact inter_subset_right
        exact Measure.mono_null subs no_A
      have Ioo_sdiff_subs_eq_points : Ioo a b \ ⋃ i : Fin m, J i = ⋃ i : Fin (m - 1), {j₁ i} := by
        have aux := interval_sdiff_subintervals_eq_endpoints (m - 1)
        have j₀0_eq_a : j₀ 0 = a := by field
        have j₁_m_sub_one_eq_b : j₁ (m - 1) = b := by
          unfold j₁
          show a + (b - a) * ((((m - 1 : ℕ) : ℝ) + 1) / m) = b
          have m_ne_zero : m ≠ 0 := by exact Nat.ne_zero_of_lt m_pos
          have : (((m - 1 : ℕ) : ℝ) + 1) / m = 1 := by
            norm_num [Nat.cast_sub m_pos]
            exact m_ne_zero
          rw [this]
          field
        rw [j₀0_eq_a, j₁_m_sub_one_eq_b, Nat.sub_one_add_one (by positivity)] at aux
        exact aux
      rw [Ioo_sdiff_subs_eq_points]
      rw [measure_null_iff_singleton]
      · exact fun x a ↦ volume_singleton
      · apply Set.countable_iUnion
        exact (fun i ↦ countable_singleton (j₁ ↑i))
  by_contra hc
  change ¬∃ i : Fin m, volume (J i) < r * volume (A ∩ J i) at hc
  rw [not_exists] at hc
  have contradiction : r * volume (A ∩ Ioo a b) ≤ volume (Ioo a b) := calc
        r * volume (A ∩ Ioo a b)
    _ = r * volume (A ∩ ⋃ (i : Fin m), J i) := by rw [interval_eq_subintervals]
    _ = r * volume (⋃ (i : Fin m), A ∩ J i) := by rw [Set.inter_iUnion]
    _ ≤ r * ∑ i : Fin m, volume (A ∩ J i)   := by grw [MeasureTheory.measure_iUnion_fintype_le]
    _ = ∑ i : Fin m, r * volume (A ∩ J i)   := by rw [Finset.mul_sum]
    _ ≤ ∑ i : Fin m, volume (J i)           := Finset.sum_le_sum fun i hi ↦ le_of_not_gt (hc i)
    _ ≤ ∑' i : Fin m, volume (J i)          := ENNReal.sum_le_tsum Finset.univ
    _ = volume (⋃ i : Fin m, J i)           := (MeasureTheory.measure_iUnion J_disj (by aesop)).symm
    _ ≤ volume (Ioo a b)                    := MeasureTheory.measure_mono (iUnion_subset Ji_sub_Ioo)
  exact (Std.not_lt.mpr contradiction) h

lemma isPreconnected_of_Ioo_subset_of_subset_Icc
    {J : Set ℝ} {a b : ℝ} (J_ge : Ioo a b ⊆ J) (J_le : J ⊆ Icc a b) :
    IsPreconnected J := by
  sorry

lemma isConnected_of_Ioo_subset_of_subset_Icc
    {J : Set ℝ} {a b : ℝ} (hab : a < b) (J_ge : Ioo a b ⊆ J) (J_le : J ⊆ Icc a b) :
    IsConnected J :=
  ⟨(nonempty_Ioo.mpr hab).mono J_ge, isPreconnected_of_Ioo_subset_of_subset_Icc J_ge J_le⟩

lemma union_add_self_subset_Icc_of_subset_Icc
    {J : Set ℝ} {a b : ℝ} (J_le : J ⊆ Icc a b) (t : ℝ) :
    J ∪ ({t} + J) ⊆ Icc (min a (a + t)) (max b (b + t)) := by
  intro x hx
  cases' hx with hx hx
  · exact ⟨min_le_of_left_le (J_le hx).1, le_max_of_le_left (J_le hx).2⟩
  · refine ⟨min_le_of_right_le ?_, le_max_of_le_right ?_⟩
    · simp only [singleton_add, image_add_left, mem_preimage] at hx
      linarith [(J_le hx).1]
    · simp only [singleton_add, image_add_left, mem_preimage] at hx
      linarith [(J_le hx).2]

lemma Ioo_subset_union_add_self_of_Ioo_subset
    {J : Set ℝ} {a b : ℝ} (J_ge : Ioo a b ⊆ J) (t : ℝ) (ht : |t| < b - a) :
    Ioo (min a (a + t)) (max b (b + t)) ⊆ J ∪ ({t} + J) := by
  sorry -- TODO: Add issue.

lemma volume_union_add_self_ge_of_Ioo_subset
    {J : Set ℝ} {a b : ℝ} (hab : a ≤ b) (J_ge : Ioo a b ⊆ J) (t : ℝ) (ht : |t| < b - a) :
    ENNReal.ofReal (b - a + |t|) ≤ volume (J ∪ ({t} + J)) := by
  sorry

lemma volume_union_add_self_le_of_subset_Icc
    {J : Set ℝ} {a b : ℝ} (hab : a ≤ b) (J_le : J ⊆ Icc a b) (t : ℝ) :
    volume (J ∪ ({t} + J)) ≤ ENNReal.ofReal (b - a + |t|) := by
  sorry

lemma volume_singleton_add {J : Set ℝ} (x : ℝ) (J_mble : MeasurableSet J):
    volume ({x} + J) = volume J := by
  have meas_preserving :
      (Measure.map (fun x_1 => -x + x_1) volume) J = volume J :=
     DFunLike.congr (MeasureTheory.measurePreserving_add_left volume (-x)).map_eq rfl
  have map_volume_eq_volume_of_pullback :
      (Measure.map (fun x_1 => -x + x_1) volume) J = volume ((fun x_1 => -x + x_1) ⁻¹' J) :=
    MeasureTheory.Measure.map_apply (μ := volume) (measurable_const_add (-x)) J_mble
  rw [Set.singleton_add, ← meas_preserving, map_volume_eq_volume_of_pullback,
      ← Set.image_add_left, ← Set.singleton_add]

lemma measurable_iff_measurable_singleton_add (x : ℝ) (J : Set ℝ) :
    MeasurableSet J ↔ MeasurableSet ({x} + J) := by
  rw [singleton_add, MeasurableEmbedding.measurableSet_image (measurableEmbedding_addLeft x)]

open TopologicalSpace ENNReal in
lemma exists_Ioo_subset_diff_self_of_measure_pos_lt_top
    {A : Set ℝ} (A_mble : MeasurableSet A)
    (A_pos : 0 < volume A) (A_lt_top : volume A < ⊤) :
    ∃ δ > 0, Ioo (-δ) δ ⊆ A - A := by
  have A_ne_top : volume A ≠ ⊤ := LT.lt.ne_top A_lt_top
  have c₁_ne_top : (4 / 3 : ℝ≥0∞) ≠ ⊤ :=
    div_ne_top (Ne.symm ENNReal.top_ne_ofNat) (Ne.symm (NeZero.ne' 3))
  have c₂_ne_top : (3 / 4 : ℝ≥0∞) ≠ ⊤ :=
    div_ne_top (Ne.symm ENNReal.top_ne_ofNat) (Ne.symm (NeZero.ne' 4))
  have c₃_ne_top : (3 / 4 * 2 : ℝ≥0∞) ≠ ⊤ :=
    mul_ne_top c₂_ne_top (Ne.symm top_ne_ofNat)
  have c₄_ne_top : (3 / 2 : ℝ≥0∞) ≠ ⊤ :=
    div_ne_top (Ne.symm top_ne_ofNat) (Ne.symm (NeZero.ne' 2))
  have const_mul_A_ne_top : (4 / 3 : ENNReal) * volume A ≠ ⊤ := by
    exact mul_ne_top c₁_ne_top A_ne_top
  have A_lt_const_mul_A : volume A < 4 / 3 * volume A := by
    have t := mul_lt_mul_of_pos_left
      (by norm_num : (1 : ℝ) < 4 / 3)
      (ENNReal.toReal_pos_iff.mpr ⟨A_pos, A_lt_top⟩)
    rw [mul_one] at t
    apply (ENNReal.toReal_lt_toReal A_ne_top const_mul_A_ne_top).mp
    simpa [ENNReal.toReal_mul, const_mul_A_ne_top, A_ne_top, mul_comm] using t

  obtain ⟨U, U_superset_A, U_open, U_lt_const_mul_A⟩ :=
    exists_isOpen_lt_of_lt (μ := volume) A ((4 / 3) * (volume A)) A_lt_const_mul_A

  let comps := {C : Set ℝ | ∃ x ∈ U, C = connectedComponentIn U x}
  have U_eq_union_comps : U = ⋃₀ comps := eq_sUnion_connectedComponentIn U
  have comps_countable : Countable comps :=
    IsOpen.countable_setOf_connectedComponentIn U_open
  have comps_disjoint : comps.Pairwise Disjoint := pairwise_disjoint_connectedComponentIn U
  have comps_open : ∀ c ∈ comps, IsOpen c := by
    intro c c_in_comps
    obtain ⟨_, _, c_is_comp⟩ := c_in_comps
    simpa [c_is_comp] using IsOpen.connectedComponentIn U_open

  have union_S_eq_U' : ⋃ (i : { c : Set ℝ // c ∈ comps}), i.val = U := by
    rw [← Set.sUnion_eq_iUnion, U_eq_union_comps]

  have ex_comp_with_prop : ∃ c ∈ comps, volume c < 4 / 3 * volume (A ∩ c) := by
    have (h : ∀ c ∈ comps, 4 / 3 * volume (A ∩ c) ≤ volume c) : 4 / 3 * volume A ≤ volume U := calc
      4 / 3 * volume A
      _ = 4 / 3 * volume (A ∩ U) := by rw [← left_eq_inter.mpr U_superset_A]
      _ = 4 / 3 * volume (A ∩ ⋃ (i : { c : Set ℝ // c ∈ comps }), i.val) := by rw [union_S_eq_U']
      _ = 4 / 3 * volume (⋃ (i : { c : Set ℝ // c ∈ comps }), A ∩ i.val) := by rw [inter_iUnion]
      _ = 4 / 3 * ∑' (i : { c // c ∈ comps }), volume (A ∩ i.val) := by
        have h :
          volume (⋃ (i : { c // c ∈ comps}), (A ∩ ·) i) =
            ∑' (i : {c // c∈ comps }), volume ((A ∩ ·) i) := by
          refine (@measure_iUnion _ _ _ _ ?_ _ ?_ ?_)
          · exact comps_countable
          · intro i j hij
            suffices toshow : Disjoint (i : Set ℝ) (j : Set ℝ)
              from Disjoint.inter_right' A (Disjoint.inter_left' A toshow)
            exact comps_disjoint i.prop j.prop (Subtype.coe_ne_coe.mpr hij)
          · intro i
            exact MeasurableSet.inter A_mble (IsOpen.measurableSet (comps_open i i.prop))
        rw [h]
      _ = ∑' (i : { c // c ∈ comps }), 4 / 3 * volume (A ∩ i.val) := by rw [ENNReal.tsum_mul_left]
      _ ≤ ∑' (i : { c // c ∈ comps }), volume i.val := by grw [h]; exact Subtype.coe_prop i
      _ = volume (⋃ (i : { c // c ∈ comps }), i.val) := by
        refine (@measure_iUnion _ _ _ _ ?_ _ ?_ ?_).symm
        · exact comps_countable
        · show Pairwise (Function.onFun Disjoint Subtype.val)
          exact (pairwise_subtype_iff_pairwise_set comps Disjoint).mpr comps_disjoint
        · exact fun c ↦ MeasurableSpace.measurableSet_generateFrom (comps_open c.val c.prop)
      _ = volume U := by rw [union_S_eq_U']
    have contrapositive :
        volume U < 4 / 3 * volume A → ∃ c ∈ comps, volume c < 4 / 3 * volume (A ∩ c) := by
      rw [← Std.not_le, not_imp_comm]
      simpa
    exact contrapositive U_lt_const_mul_A

  obtain ⟨c, ⟨c_in_comps, c_lt_const_mul_A_inter_c⟩⟩ := ex_comp_with_prop
  have c_is_open : IsOpen c := comps_open c c_in_comps
  obtain ⟨_, _, c_is_comp⟩ := c_in_comps
  have c_is_connected : IsConnected c := by
    rwa [c_is_comp, isConnected_connectedComponentIn_iff]
  have c_lt_top : volume c < ⊤ := lt_top_of_lt c_lt_const_mul_A_inter_c
  have c_mble : MeasurableSet c := MeasurableSpace.measurableSet_generateFrom c_is_open
  have c_pos : 0 < (volume c).toReal := by
    apply ENNReal.toReal_pos
    · apply IsOpen.measure_ne_zero volume
      · exact c_is_open
      · rwa [c_is_comp, connectedComponentIn_nonempty_iff]
    · suffices toshow : volume c < ⊤ from LT.lt.ne_top c_lt_const_mul_A_inter_c
      calc
            volume c
        _ < 4 / 3 * volume (A ∩ c) := gt_iff_lt.mp c_lt_const_mul_A_inter_c
        _ ≤ 4 / 3 * volume A := by grw [measure_mono inter_subset_left]
        _ < ⊤ := Ne.lt_top' (id (Ne.symm const_mul_A_ne_top))
  let δ := 1 / 2 * (volume c).toReal
  use δ; constructor; positivity
  intro x x_in_Ioo

  have vol_outer : volume (({x} + c) ∪ c) ≤ 3 / 2 * volume c := by
    obtain ⟨x_lb, x_ub⟩ := Set.mem_Ioo.mp x_in_Ioo
    have x_abs_lt : |x| < 1 / 2 * (volume c).toReal := abs_lt.mpr x_in_Ioo
    obtain ⟨a, b, c_is_Ioo⟩ : ∃ a b : ℝ, c = Ioo a b :=
      eq_Ioo_of_isOpen_of_isConnected_of_isFinite c_is_open c_is_connected c_lt_top
    have c_nonempty : c.Nonempty :=
      (IsOpen.measure_pos_iff (μ := volume) c_is_open).mp
        ((toReal_lt_toReal zero_ne_top (LT.lt.ne_top c_lt_const_mul_A_inter_c)).mp
          c_pos)
    obtain ⟨t, t_in_c⟩ : ∃ t : ℝ, t ∈ c := nonempty_def.mp c_nonempty
    rw [c_is_Ioo] at t_in_c x_abs_lt
    obtain ⟨a_lt_t, t_lt_b⟩ := Set.mem_Ioo.mp t_in_c
    have a_lt_b : a < b := Std.lt_trans a_lt_t t_lt_b
    have x_abs_lt : |x| < 1 / 2 * (b - a) := by
      rw [Real.volume_Ioo, toReal_ofReal (by positivity)] at x_abs_lt
      exact x_abs_lt
    let J := Icc a b
    have : ENNReal.ofReal (b - a + |x|) ≤ 3 / 2 * volume c := calc
          ENNReal.ofReal (b - a + |x|)
      _ ≤ ENNReal.ofReal (b - a + 1 / 2 * (b - a)) := by grw [x_abs_lt]
      _ = ENNReal.ofReal (3 / 2 * (b - a)) := by ring_nf
      _ = ENNReal.ofReal (3 / 2) * ENNReal.ofReal (b - a) := ENNReal.ofReal_mul (by positivity)
      _ = ENNReal.ofReal 3 / (ENNReal.ofReal 2) * ENNReal.ofReal (b - a) := by
        rw [ENNReal.ofReal_div_of_pos (by positivity)]
      _ = 3 / 2 * ENNReal.ofReal (b - a) := by rw [ofReal_ofNat 3, ofReal_ofNat 2]
      _ = 3 / 2 * volume c := by rw [c_is_Ioo, Real.volume_Ioo]
    have : volume ({x} + c ∪ c) ≤ 3 / 2 * volume c := by
      grw [union_comm, ← this]
      apply volume_union_add_self_le_of_subset_Icc
      · exact Std.le_of_lt a_lt_b
      · rw [c_is_Ioo]
        exact Ioo_subset_Icc_self
    exact this

  have vol_outer_finite : volume (({x} + c) ∪ c) < ⊤ := by
    grw [MeasureTheory.measure_union_le, ENNReal.add_lt_top]
    rw [volume_singleton_add x c_mble]
    constructor <;> finiteness

  have inner₁ : A ∩ c ⊆ ({x} + c) ∪ c := by
    have : A ∩ c ⊆ c := by exact inter_subset_right
    exact subset_union_of_subset_right this ({x} + c)

  have inner₂ : {x} + (A ∩ c) ⊆ ({x} + c) ∪ c := by
    have : {x} + (A ∩ c) ⊆ {x} + c := by
      apply add_subset_add
      · trivial
      · exact inter_subset_right
    exact subset_union_of_subset_left this c

  have vol_inner₁ : 3 / 4 * volume c < volume (A ∩ c) := by
    have aux : (3 / 4 * volume c).toReal < (volume (A ∩ c)).toReal := by
      have c_lt_const_mul_A_inter_c_toReal :
          (volume c).toReal < (4 / 3 * volume (A ∩ c)).toReal := (ENNReal.toReal_lt_toReal
            (LT.lt.ne_top c_lt_top)
            (ENNReal.mul_ne_top c₁_ne_top (measure_inter_ne_top_of_left_ne_top A_ne_top))).mpr
              c_lt_const_mul_A_inter_c
      simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat]
        at c_lt_const_mul_A_inter_c_toReal
      linarith
    have h₁ : 3 / 4 * volume c ≠ ⊤ := ENNReal.mul_ne_top c₂_ne_top (LT.lt.ne_top c_lt_top)
    have h₂ : volume (A ∩ c) ≠ ⊤ := measure_inter_ne_top_of_left_ne_top A_ne_top
    exact (ENNReal.toReal_lt_toReal h₁ h₂).mp aux

  have vol_inner₂ : 3 / 4 * volume c < volume ({x} + (A ∩ c)) := by
    rw [volume_singleton_add x (MeasurableSet.inter A_mble c_mble)]
    exact vol_inner₁

  have : ∃ a : ℝ, a ∈ (A ∩ c) ∩ ({x} + (A ∩ c)) := by
    apply MeasureTheory.nonempty_inter_of_measure_lt_add (μ := volume) (u := ({x} + c) ∪ c)
    · exact (measurable_iff_measurable_singleton_add x (A ∩ c)).mp
              (MeasurableSet.inter A_mble c_mble)
    · assumption
    · assumption
    · grw [vol_outer]
      have t := ENNReal.add_lt_add vol_inner₁ vol_inner₂
      have ennreal_eq : (3 : ℝ≥0∞) / 4 * 2 = 3 / 2 := calc
        (3 : ENNReal) / 4 * 2
        _ = ENNReal.ofReal ((3 : ℝ≥0∞) / 4 * 2).toReal := (ENNReal.ofReal_toReal c₃_ne_top).symm
        _ = ENNReal.ofReal ((3 : ℝ) / 4 * 2) := by simp only [toReal_mul, toReal_div, toReal_ofNat]
        _ = ENNReal.ofReal ((3 : ℝ) / 2) := by norm_num
        _ = ENNReal.ofReal ((3 : ℝ≥0∞) / 2).toReal := by simp [toReal_div, toReal_ofNat]
        _ = (3 : ENNReal) / 2 := ENNReal.ofReal_toReal c₄_ne_top
      rwa [← left_distrib, ← two_mul, ← mul_assoc, ennreal_eq] at t
  obtain ⟨a, a_in_A, a_in_x_plus_A⟩ := this

  rcases a_in_x_plus_A with ⟨x', ⟨x'_in_x, ⟨a', ⟨a'_mem, a'_sum⟩⟩⟩⟩
  have x'_eq_x : x' = x := by trivial
  beta_reduce at a'_sum
  have : x = a - a' := by simp [x'_eq_x, ← a'_sum]
  rw [this]
  apply Set.sub_mem_sub
  · exact mem_of_mem_inter_left a_in_A
  · exact mem_of_mem_inter_left a'_mem

-- TODO: immediate via exists_Ioo_subset_diff_of_measure_pos,
-- should this just be moved after it?
lemma exists_Ioo_subset_diff_self_of_measure_pos {A : Set ℝ}
    (A_mble : MeasurableSet A) (A_pos : 0 < volume A) :
    ∃ δ > 0, Ioo (-δ) δ ⊆ A - A := by
  obtain ⟨B, B_mble, B_subset_A, B_pos, B_lt_top⟩ :=
    Measure.exists_subset_measure_lt_top A_mble A_pos
  obtain ⟨δ, δ_pos, Ioo_subset_diff_self_B⟩ :=
    exists_Ioo_subset_diff_self_of_measure_pos_lt_top B_mble B_pos B_lt_top
  use δ; constructor; exact δ_pos
  exact Subset.trans Ioo_subset_diff_self_B (sub_subset_sub B_subset_A B_subset_A)

open TopologicalSpace ENNReal in
lemma exists_Ioo_subset_diff_of_measure_pos {A B : Set ℝ}
    (A_mble : MeasurableSet A) (A_pos : 0 < volume A)
    (B_mble : MeasurableSet B) (B_pos : 0 < volume B) :
    ∃ (a b : ℝ), a < b ∧ Ioo a b ⊆ A - B := by
  obtain ⟨A', A'_mble, A'_subset_A, A'_pos, A'_lt_top⟩ :=
    Measure.exists_subset_measure_lt_top A_mble A_pos
  obtain ⟨B', B'_mble, B'_subset_B, B'_pos, B'_lt_top⟩ :=
    Measure.exists_subset_measure_lt_top B_mble B_pos
  obtain ⟨I, ⟨I_conn, I_nonempty, I_lt_r_mul_A'_inter_I⟩⟩ :=
    exists_interval_measure_inter_gt_mul_measure
      A'_mble A'_pos A'_lt_top (show 1 < (4 : ℝ) / 3 by norm_num)
  obtain ⟨J, ⟨J_conn, J_nonempty, J_lt_r_mul_B'_inter_J⟩⟩ :=
    exists_interval_measure_inter_gt_mul_measure
      B'_mble B'_pos B'_lt_top (show 1 < (4 : ℝ) / 3 by norm_num)
  have I_open : IsOpen I := sorry
  have J_open : IsOpen J := sorry
  obtain ⟨i₀, i₁, I_is_Ioo⟩ : ∃ i₀ i₁ : ℝ, I = Ioo i₀ i₁ :=
      eq_Ioo_of_isOpen_of_isConnected_of_isFinite
        I_open I_conn (lt_top_of_lt I_lt_r_mul_A'_inter_I)
  obtain ⟨j₀, j₁, J_is_Ioo⟩ : ∃ j₀ j₁ : ℝ, J = Ioo j₀ j₁ :=
      eq_Ioo_of_isOpen_of_isConnected_of_isFinite
        J_open J_conn (lt_top_of_lt J_lt_r_mul_B'_inter_J)
  have i₀_lt_i₁ : i₀ < i₁ := by
    obtain ⟨x, x_in_I⟩ := IsConnected.nonempty I_conn
    rw [I_is_Ioo, mem_Ioo] at x_in_I
    linarith
  have j₀_lt_j₁ : j₀ < j₁ := by
    obtain ⟨x, x_in_J⟩ := IsConnected.nonempty J_conn
    rw [J_is_Ioo, mem_Ioo] at x_in_J
    linarith
  obtain ⟨q, lt_q, q_lt⟩ :
      ∃ q : ℚ, ((j₁ - j₀) / (i₁ - i₀)) < q ∧ q < (2 * ((j₁ - j₀) / (i₁ - i₀))) := by
    apply exists_rat_btwn
    linarith [div_pos (sub_pos.mpr j₀_lt_j₁) (sub_pos.mpr i₀_lt_i₁)]
  have q_pos : 0 < (q : ℝ) := by
    suffices 0 < (i₁ - i₀) / (j₁ - j₀) by linarith
    exact div_pos (sub_pos.mpr i₀_lt_i₁) (sub_pos.mpr j₀_lt_j₁)
  have q_num_pos : 0 < q.num.toNat := by
    suffices num_pos : 0 < q.num from Int.pos_iff_toNat_pos.mp num_pos
    exact Rat.num_pos.mpr (by exact_mod_cast q_pos)
  rw [I_is_Ioo] at I_lt_r_mul_A'_inter_I
  rw [J_is_Ioo] at J_lt_r_mul_B'_inter_J
  obtain ⟨i, i_ineq⟩ :=
    exists_subinterval_preserving_volume_property i₀_lt_i₁ I_lt_r_mul_A'_inter_I (Rat.den_pos q)
  obtain ⟨j, j_ineq⟩ :=
    exists_subinterval_preserving_volume_property j₀_lt_j₁ J_lt_r_mul_B'_inter_J q_num_pos
  let a := (i₀ + (i₁ - i₀) * (i / q.den))
  let b := (i₀ + (i₁ - i₀) * ((i + 1) / q.den))
  let c := j₀ + (j₁ - j₀) * (j / q.num.toNat)
  let d := j₀ + (j₁ - j₀) * ((j + 1) / q.num.toNat)
  change volume (Ioo a b) < ENNReal.ofReal (4 / 3) * volume (A' ∩ Ioo a b) at i_ineq
  change volume (Ioo c d) < ENNReal.ofReal (4 / 3) * volume (B' ∩ Ioo c d) at j_ineq
  obtain ⟨cd_lt_ab, half_ab_lt_cd⟩ :
      d - c < b - a ∧ ENNReal.ofReal (1 / 2) * volume (Ioo a b) < volume (Ioo c d) := by
    unfold a b c d
    
    have hl : i₀ + (i₁ - i₀) * ((↑↑i + 1) / ↑q.den) - (i₀ + (i₁ - i₀) * (↑↑i / ↑q.den))
            = (i₁ - i₀) / q.den := by ring    
    have hr : j₀ + (j₁ - j₀) * ((j + 1) / ↑q.num.toNat) - (j₀ + (j₁ - j₀) * (j / ↑q.num.toNat))
            = (j₁ - j₀) / q.num.toNat := by ring
    have q_revive : (q.num.toNat / q.den : ℝ) = (q : ℝ) := by
      have num_tonat_eq_num : (q.num.toNat : ℝ) = (q.num : ℝ) := by
        have num_nonneg : 0 ≤ q.num := Rat.num_nonneg.mpr (Rat.le_of_lt (by exact_mod_cast q_pos))
        exact_mod_cast Int.toNat_of_nonneg num_nonneg
      simp [num_tonat_eq_num, Rat.cast_def]
    repeat rw [Real.volume_Ioo]
    rw [hl, hr]
    constructor
    · have num_i₁_sub_i₀_lmul : q.num.toNat / (i₁ - i₀) * ((j₁ - j₀) / q.num.toNat) <
               q.num.toNat / (i₁ - i₀) * ((i₁ - i₀) / q.den)
           ↔ (j₁ - j₀) / ↑q.num.toNat < (i₁ - i₀) / q.den :=
        mul_lt_mul_iff_of_pos_left (by positivity)
      
      have left_simplified : q.num.toNat / (i₁ - i₀) * ((j₁ - j₀) / q.num.toNat)
                           = (j₁ - j₀) / (i₁ - i₀) := by field
      have right_simplified : q.num.toNat / (i₁ - i₀) * ((i₁ - i₀) / q.den)
                            = q.num.toNat / q.den := by
        field_simp
        apply div_self
        positivity
      rwa [← num_i₁_sub_i₀_lmul, left_simplified, right_simplified, q_revive]
    · have zero_lt : 0 < (j₁ - j₀) / q.num.toNat := by positivity
      rw [← ENNReal.ofReal_mul (by norm_num),
          ofReal_lt_ofReal_iff zero_lt]
      
      have num_two_i₁_sub_i₀_lmul :
            (q.num.toNat * 2 / (i₁ - i₀)) * (1 / 2 * ((i₁ - i₀) / q.den)) <
              (q.num.toNat * 2 / (i₁ - i₀)) * ((j₁ - j₀) / q.num.toNat)
          ↔ 1 / 2 * ((i₁ - i₀) / ↑q.den) < (j₁ - j₀) / ↑q.num.toNat :=
        mul_lt_mul_iff_of_pos_left (by positivity)
      have left_simplified : (q.num.toNat * 2 / (i₁ - i₀)) * (1 / 2 * ((i₁ - i₀) / q.den))
                           = q.num.toNat / q.den := by
        field_simp
        apply div_self
        positivity
      have right_simplified : (q.num.toNat * 2 / (i₁ - i₀)) * ((j₁ - j₀) / q.num.toNat)
                            = 2 * ((j₁ - j₀) / (i₁ - i₀)) := by field
      rwa [← num_two_i₁_sub_i₀_lmul, left_simplified, q_revive, right_simplified]
  let Δ := Ioo (a - c) (b - d)
  use a - c, b - d; constructor; linarith
  intro x x_in_Δ
  have outer_vol :
      volume (Ioo a b) <
        ((8 / 9) : ℝ≥0∞) * (volume (A' ∩ Ioo a b) + volume ({x} + (B' ∩ Ioo c d))) := calc
        volume (Ioo a b)
    _ = (2 / 3 : ℝ≥0∞) * (volume (Ioo a b) + ENNReal.ofReal (1 / 2) * volume (Ioo a b)) := sorry
    _ ≤ (2 / 3 : ℝ≥0∞) * (volume (Ioo a b) + volume (Ioo c d)) := by grw [half_ab_lt_cd]
    _ < (2 / 3 : ℝ≥0∞) * (ENNReal.ofReal (4 / 3) * volume (A' ∩ Ioo a b)
                        + ENNReal.ofReal (4 / 3) * volume (B' ∩ Ioo c d)) := by
      apply ENNReal.mul_lt_mul_right
      · norm_num
      · exact div_ne_top (Ne.symm top_ne_ofNat) (Ne.symm (NeZero.ne' 3))
      · exact ENNReal.add_lt_add i_ineq j_ineq
    _ = (8 / 9 : ℝ≥0∞) * (volume (A' ∩ Ioo a b) + volume (B' ∩ Ioo c d)) := sorry
    _ = (8 / 9 : ℝ≥0∞) * (volume (A' ∩ Ioo a b) + volume ({x} + B' ∩ Ioo c d)) := by
      rw [volume_singleton_add]
      aesop
  have inter_nonempty : ((A' ∩ Ioo a b) ∩ ({x} + (B' ∩ Ioo c d))).Nonempty := by
    apply MeasureTheory.nonempty_inter_of_measure_lt_add (μ := volume) (u := Ioo a b)
    · exact (measurable_iff_measurable_singleton_add x (B' ∩ Ioo c d)).mp
              (MeasurableSet.inter B'_mble measurableSet_Ioo)
    · exact inter_subset_right
    · have aux : {x} + Ioo c d ⊆ Ioo a b := by
        intro t ht
        rw [Set.singleton_add, Set.image_const_add_Ioo] at ht
        rw [mem_Ioo] at ht x_in_Δ ⊢
        obtain ⟨_, _⟩ := x_in_Δ
        obtain ⟨_, _⟩ := ht
        constructor <;> linarith
      grw [inter_subset_right]
      exact aux
    · grw [outer_vol]
      rw (occs := .pos [2]) [← one_mul (volume (A' ∩ Ioo a b) + volume (_ + B' ∩ Ioo c d))]
      apply ENNReal.mul_lt_mul_left
      · by_contra h
        rw [add_eq_zero] at h
        rw [h.left, h.right] at outer_vol
        simp at outer_vol
      · apply Finiteness.add_ne_top
        · suffices A'_ne_top : volume (A') ≠ ∞ from measure_inter_ne_top_of_left_ne_top A'_ne_top
          exact LT.lt.ne_top A'_lt_top
        · rw [volume_singleton_add x (MeasurableSet.inter B'_mble measurableSet_Ioo)]
          suffices B'_ne_top : volume (B') ≠ ∞ from measure_inter_ne_top_of_left_ne_top B'_ne_top
          exact LT.lt.ne_top B'_lt_top
      · rw [ENNReal.div_lt_iff] <;> norm_num
  obtain ⟨a', ⟨⟨a'_in_A', a'_in_ab⟩, ⟨x', ⟨x'_in_x, ⟨b', ⟨⟨b'_in_B, b'_in_cd⟩, b'_sum⟩⟩⟩⟩⟩⟩ :=
    inter_nonempty
  rw [show x = a' - b' by simp [← b'_sum, show x' = x by trivial]]
  exact Set.sub_mem_sub
    (mem_of_subset_of_mem A'_subset_A a'_in_A') (mem_of_subset_of_mem B'_subset_B b'_in_B)

lemma exists_Ioo_subset_add_of_measure_pos {A : Set ℝ}
    (A_mble : MeasurableSet A) (A_pos : 0 < volume A) :
    ∃ (a b : ℝ), a < b ∧ Ioo a b ⊆ A + A := by
  obtain ⟨a, b, a_lt_b, hab⟩ := exists_Ioo_subset_diff_of_measure_pos
        A_mble A_pos A_mble.neg (by simpa only [Measure.measure_neg] using A_pos)
  refine ⟨a, b, a_lt_b, by simpa only [sub_neg_eq_add] using hab⟩

lemma eq_top_of_subgroup_of_measure_pos {S : AddSubgroup ℝ}
    {A : Set ℝ} (A_le_S : A ⊆ S) (A_mble : MeasurableSet A) (A_pos : 0 < volume A) :
    S = ⊤ := by
  sorry

lemma exists_forall_abs_le_of_additive_of_le_on_measure_pos
    {f : ℝ → ℝ} (f_add : ∀ t₁ t₂, f (t₁ + t₂) = f t₁ + f t₂)
    {A : Set ℝ} (A_mble : MeasurableSet A) (A_pos : 0 < volume A)
    {M : ℝ} (f_bdd_on_A : ∀ a ∈ A, f a ≤ M) :
    ∃ δ > 0, ∃ c, ∀ x ∈ Ioo (-δ) δ, |f x| ≤ c := by
  sorry

open Topology in
lemma exists_nhd_abs_le_of_additive_of_le_on_measure_pos
    {f : ℝ → ℝ} (f_add : ∀ t₁ t₂, f (t₁ + t₂) = f t₁ + f t₂)
    {A : Set ℝ} (A_mble : MeasurableSet A) (A_pos : 0 < volume A)
    {M : ℝ} (f_bdd_on_A : ∀ a ∈ A, f a ≤ M) :
    ∃ B ∈ 𝓝 (0 : ℝ), ∃ c, ∀ x ∈ B, |f x| ≤ c := by
  obtain ⟨δ, δ_pos, hδ⟩ :=
    exists_forall_abs_le_of_additive_of_le_on_measure_pos f_add A_mble A_pos f_bdd_on_A
  exact ⟨Ioo (-δ) δ, Ioo_mem_nhds (by linarith) δ_pos, hδ⟩

lemma linear_of_additive_of_le_on_measure_pos
    {f : ℝ → ℝ} (f_add : ∀ t₁ t₂, f (t₁ + t₂) = f t₁ + f t₂)
    {A : Set ℝ} (A_mble : MeasurableSet A) (A_pos : 0 < volume A)
    {M : ℝ} (f_bdd_on_A : ∀ a ∈ A, f a ≤ M) (x : ℝ) :
    f x = (f 1) * x := by
  sorry

open ENNReal in
lemma linear_of_additive_of_measurable
    {f : ℝ → ℝ} (f_add : ∀ t₁ t₂, f (t₁ + t₂) = f t₁ + f t₂) (f_mble : Measurable f) (x : ℝ) :
    f x = (f 1) * x := by
  set As : ℕ → Set ℝ := fun n ↦ {y | f y ≤ n} with def_As
  have cover : ⋃ n, As n = ⊤ := by
    ext x
    simp [exists_nat_ge (f x), def_As]
  have As_mble (n : ℕ) : MeasurableSet (As n) := f_mble measurableSet_Iic
  obtain ⟨n, hn⟩ : ∃ n, 0 < volume (As n) := by
    apply exists_measure_pos_of_not_measure_iUnion_null
    simp [cover]
  exact linear_of_additive_of_le_on_measure_pos f_add (As_mble n) hn (M := n) (by simp [def_As]) x

/-- A measurable additive map ℝ → ℝ is linear.
(The only measurable solutions to the Cauchy-Hamel functional equation are the obvious ones.) -/
lemma eq_const_mul_of_additive_of_measurable {f : ℝ → ℝ}
    (f_add : ∀ s₁ s₂, f (s₁ + s₂) = f s₁ + f s₂) (f_mble : Measurable f) :
    ∃ α, f = fun s ↦ α * s := by
  use f 1
  ext x
  exact linear_of_additive_of_measurable f_add f_mble x

/-- A measurable multiplicative map ℝ → (0,+∞) is of the form s ↦ exp(α * s) for some α ∈ ℝ.
(The only measurable solutions to the multiplicative version of the Cauchy-Hamel functional
equation are the obvious ones.) -/
lemma eq_exp_const_mul_of_multiplicative_of_measurable {f : ℝ → ℝ} (f_pos : ∀ s, 0 < f s)
    (f_multiplicative : ∀ s₁ s₂, f (s₁ + s₂) = f s₁ * f s₂) (f_mble : Measurable f) :
    ∃ α, f = fun s ↦ exp (α * s) := by
  let g := fun s ↦ log (f s)
  have f_eq_exp_g (s) : f s = exp (g s) := by
    simpa [g] using (exp_log (f_pos s)).symm
  have g_mble : Measurable g := measurable_log.comp f_mble
  have g_additive (s₁ s₂) : g (s₁ + s₂) = g s₁ + g s₂ := by
    simpa only [g, f_multiplicative] using log_mul (f_pos _).ne.symm (f_pos _).ne.symm
  obtain ⟨α, key⟩ := eq_const_mul_of_additive_of_measurable g_additive g_mble
  refine ⟨α, by ext s ; rw [f_eq_exp_g, key]⟩

end cauchy_hamel_functional_equation


section one_parameter_subgroups_of_affine_transformations

/-- The homomorphism `ℝ → AffineIncrEquiv` given by `s ↦ Aₛ`, where `Aₛ x = x + β * s`.
(`β` is a real parameter: each `β` gives a different (but related) homomorphism) -/
noncomputable def AffineIncrEquiv.homOfIndex₀ (β : ℝ) :
    MonoidHom (Multiplicative ℝ) AffineIncrEquiv where
  toFun s := .mkOfCoefs zero_lt_one (s.toAdd * β)
  map_one' := by ext x ; simp
  map_mul' s₁ s₂ := by
    ext x
    simp
    ring

/-- The homomorphism `ℝ → AffineIncrEquiv` given by `s ↦ Aₛ`, where
`Aₛ x = exp(α * s) * (x - c) + c`.
(`α c` are real parameters: each `α c` give a different homomorphism) -/
noncomputable def AffineIncrEquiv.homOfIndex (α c : ℝ) :
    MonoidHom (Multiplicative ℝ) AffineIncrEquiv where
  toFun s := .mkOfCoefs (show 0 < Real.exp (s.toAdd * α) from Real.exp_pos _)
              (c * (1 - Real.exp (s.toAdd * α)))
  map_one' := by ext x ; simp
  map_mul' s₁ s₂ := by
    ext x
    simp [add_mul, Real.exp_add]
    ring

@[simp] lemma AffineIncrEquiv.homOfIndex₀_coefs_fst {β s : ℝ} :
    (homOfIndex₀ β s).coefs.1 = 1 := by
  simp [homOfIndex₀, MonoidHom.coe_mk, OneHom.coe_mk, coefs_fst_mkOfCoefs]

@[simp] lemma AffineIncrEquiv.homOfIndex₀_coefs_snd {β s : ℝ} :
    (homOfIndex₀ β s).coefs.2 = s * β := by
  simp only [homOfIndex₀, MonoidHom.coe_mk, OneHom.coe_mk, coefs_snd_mkOfCoefs]
  congr

@[simp] lemma AffineIncrEquiv.homOfIndex_coefs_fst {α c s : ℝ} :
    (homOfIndex α c s).coefs.1 = Real.exp (s * α) := by
  simp only [homOfIndex, MonoidHom.coe_mk, OneHom.coe_mk, coefs_fst_mkOfCoefs, Real.exp_eq_exp]
  congr

@[simp] lemma AffineIncrEquiv.homOfIndex_coefs_snd {α c s : ℝ} :
    (homOfIndex α c s).coefs.2 = c * (1 - Real.exp (s * α)) := by
  simp only [homOfIndex, MonoidHom.coe_mk, OneHom.coe_mk, coefs_snd_mkOfCoefs]
  congr

@[simp] lemma AffineIncrEquiv.homOfIndex₀_zero' (β : ℝ) :
    homOfIndex₀ β (.ofAdd 0) = 1 :=
  map_one ..

@[simp] lemma AffineIncrEquiv.homOfIndex₀_zero (β : ℝ) :
    homOfIndex₀ β (@OfNat.ofNat ℝ 0 Zero.toOfNat0) = 1 :=
  map_one ..

lemma AffineIncrEquiv.homOfIndex₀_zero_apply' (β : ℝ) (x : ℝ) :
    homOfIndex₀ β (.ofAdd 0) x = x := by
  simp

lemma AffineIncrEquiv.homOfIndex₀_zero_apply (β : ℝ) (x : ℝ) :
    homOfIndex₀ β (@OfNat.ofNat ℝ 0 Zero.toOfNat0) x = x := by
  simp

lemma AffineIncrEquiv.homOfIndex₀_add (β : ℝ) (s₁ s₂ : ℝ) :
    homOfIndex₀ β (s₁ + s₂) = homOfIndex₀ β s₁ * homOfIndex₀ β s₂ :=
  map_mul ..

@[simp] lemma AffineIncrEquiv.homOfIndex₀_inv (β : ℝ) (s : ℝ) :
    (homOfIndex₀ β s)⁻¹ = homOfIndex₀ β (-s) := by
  have obs := homOfIndex₀_add β s (-s)
  simp only [add_neg_cancel, homOfIndex₀_zero] at obs
  exact DivisionMonoid.inv_eq_of_mul _ _ obs.symm

@[simp] lemma AffineIncrEquiv.homOfIndex₀_add_apply {β : ℝ} {s₁ s₂ : ℝ} (x : ℝ) :
    homOfIndex₀ β (s₁ + s₂) x = homOfIndex₀ β s₁ (homOfIndex₀ β s₂ x) := by
  simp only [homOfIndex₀_add, mul_apply_eq_comp_apply]

lemma AffineIncrEquiv.homOfIndex₀_eq_homOfIndex₀_one_mul {β s : ℝ} :
    homOfIndex₀ β s = homOfIndex₀ 1 (β * s) := by
  ext x
  simp [mul_comm]

lemma AffineIncrEquiv.conjugate_homOfIndex₀ (A : AffineIncrEquiv) (β : ℝ) (s : ℝ) :
    A * homOfIndex₀ β s * A⁻¹ = homOfIndex₀ (β * A.coefs.1) s := by
  sorry -- **Issue #46**

@[simp] lemma AffineIncrEquiv.homOfIndex_zero' (α c : ℝ) :
    homOfIndex α c (.ofAdd 0) = 1 :=
  map_one ..

@[simp] lemma AffineIncrEquiv.homOfIndex_zero (α c : ℝ) :
    homOfIndex α c (@OfNat.ofNat ℝ 0 Zero.toOfNat0) = 1 :=
  map_one ..

lemma AffineIncrEquiv.homOfIndex_zero_apply' (α c : ℝ) (x : ℝ) :
    homOfIndex α c (.ofAdd 0) x = x := by
  simp

lemma AffineIncrEquiv.homOfIndex_zero_apply (α c : ℝ) (x : ℝ) :
    homOfIndex α c (@OfNat.ofNat ℝ 0 Zero.toOfNat0) x = x := by
  simp

lemma AffineIncrEquiv.homOfIndex_add (α c : ℝ) (s₁ s₂ : ℝ) :
    homOfIndex α c (s₁ + s₂) = homOfIndex α c s₁ * homOfIndex α c s₂ :=
  map_mul ..

@[simp] lemma AffineIncrEquiv.homOfIndex_inv (α c : ℝ) (s : ℝ) :
    (homOfIndex α c s)⁻¹ = homOfIndex α c (-s) := by
  have obs := homOfIndex_add α c s (-s)
  simp only [add_neg_cancel, homOfIndex_zero] at obs
  exact DivisionMonoid.inv_eq_of_mul _ _ obs.symm

@[simp] lemma AffineIncrEquiv.homOfIndex_add_apply {α c : ℝ} {s₁ s₂ : ℝ} (x : ℝ) :
    homOfIndex α c (s₁ + s₂) x = homOfIndex α c s₁ (homOfIndex α c s₂ x) := by
  simp only [homOfIndex_add, mul_apply_eq_comp_apply]

lemma AffineIncrEquiv.homOfIndex_eq_homOfIndex_one_mul {α c s : ℝ} :
    homOfIndex α c s = homOfIndex 1 c (s * α) := by
  ext x
  simp

lemma AffineIncrEquiv.conjugate_homOfIndex (A : AffineIncrEquiv) (α c : ℝ) (s : ℝ) :
    A * homOfIndex α c s * A⁻¹ = homOfIndex α (A c) s := by
  sorry -- **Issue #46**

/-- The one-parameter subgroup of `AffineIncrEquiv` consisting of elements `Aₛ` of the form
`Aₛ x = x + β * s`, where `s ∈ ℝ`.
(`β` is a real parameter: each `β ≠ 0` in fact gives the same subgroup) -/
noncomputable def AffineIncrEquiv.subGroupOfIndex₀' (β : ℝ) :
    Subgroup AffineIncrEquiv :=
  Subgroup.map (AffineIncrEquiv.homOfIndex₀ β) ⊤

/-- The one-parameter subgroup of `AffineIncrEquiv` consisting of elements `Aₛ` of the form
`Aₛ x = x + s`, where `s ∈ ℝ`. -/
noncomputable def AffineIncrEquiv.subGroupOfIndex₀ :
    Subgroup AffineIncrEquiv :=
  Subgroup.map (AffineIncrEquiv.homOfIndex₀ 1) ⊤

@[simp] lemma AffineIncrEquiv.subGroupOfIndex₀'_eq_of_ne_zero {β : ℝ} (hβ : β ≠ 0) :
    AffineIncrEquiv.subGroupOfIndex₀' β = AffineIncrEquiv.subGroupOfIndex₀ := by
  sorry -- **Issue 44**

@[simp] lemma AffineIncrEquiv.subGroupOfIndex₀'_eq_bot :
    AffineIncrEquiv.subGroupOfIndex₀' 0 = ⊥ := by
  sorry -- **Issue 44**

@[simp] lemma AffineIncrEquiv.mem_subGroupOfIndex₀_of_no_fixed_point (A : AffineIncrEquiv)
    {α : ℝ} (hα : α ≠ 0) (c : ℝ) (hA : ∀ x, A x ≠ x) :
    A ∈ subGroupOfIndex₀ := by
  sorry -- **Issue 44**

/-- The one-parameter subgroup of `AffineIncrEquiv` consisting of elements `Aₛ` of the form
`Aₛ x = exp(α * s) * (x - c) + c` where `s ∈ ℝ`.
(`α c` are real parameters) -/
noncomputable def AffineIncrEquiv.subGroupOfIndex (α c : ℝ) :
    Subgroup AffineIncrEquiv :=
  Subgroup.map (AffineIncrEquiv.homOfIndex α c) ⊤

@[simp] lemma AffineIncrEquiv.subGroupOfIndex_eq_bot (c : ℝ) :
    subGroupOfIndex 0 c = ⊥ := by
  sorry -- **Issue 45**

@[simp] lemma AffineIncrEquiv.fixed_point_of_mem_subGroupOfIndex (A : AffineIncrEquiv)
    {α c : ℝ} (hA : A ∈ subGroupOfIndex α c):
    A c = c := by
  obtain ⟨s, _, hs⟩ := hA
  simp only [← hs, apply_eq, homOfIndex_coefs_fst, homOfIndex_coefs_snd]
  ring

@[simp] lemma AffineIncrEquiv.mem_subGroupOfIndex_iff_fixed_point (A : AffineIncrEquiv)
    {α : ℝ} (hα : α ≠ 0) (c : ℝ) :
    A ∈ subGroupOfIndex α c ↔ A c = c := by
  sorry -- **Issue 45**

/-- Functional equation for scaling coefficients of a homomorphism `f : ℝ → AffineIncrEquiv`. -/
lemma AffineIncrEquiv.homomorphism_coef_eqn_fst
    (f : MonoidHom (Multiplicative ℝ) AffineIncrEquiv) (s₁ s₂ : ℝ) :
    (f (s₁ + s₂)).coefs.1 = (f s₁).coefs.1 * (f s₂).coefs.1 := by
  simp [show f (s₁ + s₂) = f s₁ * f s₂ by rw [← f.map_mul] ; rfl]

/-- Functional equation for translation coefficients of a homomorphism `f : ℝ → AffineIncrEquiv`. -/
lemma AffineIncrEquiv.homomorphism_coef_eqn_snd
    (f : MonoidHom (Multiplicative ℝ) AffineIncrEquiv) (s₁ s₂ : ℝ) :
    (f (s₁ + s₂)).coefs.2 = (f s₁).coefs.1 * (f s₂).coefs.2 + (f s₁).coefs.2 := by
  simp [show f (s₁ + s₂) = f s₁ * f s₂ by rw [← f.map_mul] ; rfl]

open Real

lemma eq_of_functional_eqn_of_ne_zero {f : ℝ → ℝ} {α : ℝ} (α_ne_zero : α ≠ 0)
    (f_eqn : ∀ s₁ s₂, f (s₁ + s₂) = exp (α * s₁) * f s₂ + f s₁) :
    ∃ c, f = fun s ↦ c * (1 - exp (α * s)) := by
  sorry

/-- We endow the space of orientation-preserving affine isomorphisms of `ℝ` with the Borel
σ-algebra of the topology of pointwise convergence. -/
instance : MeasurableSpace AffineIncrEquiv := borel AffineIncrEquiv

instance : BorelSpace AffineIncrEquiv := ⟨rfl⟩

lemma AffineIncrEquiv.measurable_coefs_fst :
    Measurable (fun (A : AffineIncrEquiv) ↦ A.coefs.1) :=
  continuous_coefs_fst.measurable

lemma AffineIncrEquiv.measurable_coefs_snd :
    Measurable (fun (A : AffineIncrEquiv) ↦ A.coefs.2) :=
  continuous_coefs_snd.measurable

lemma AffineIncrEquiv.continuous_mkOfCoefs :
    Continuous fun (p : {a : ℝ // 0 < a} × ℝ) ↦ mkOfCoefs p.1.prop p.2 := by
  apply (continuous_induced_rng ..).mpr
  exact continuous_pi (by continuity)

lemma AffineIncrEquiv.measurable_mkOfCoefs :
    Measurable fun (p : {a : ℝ // 0 < a} × ℝ) ↦ mkOfCoefs p.1.prop p.2 := by
  have _bs1 : BorelSpace {a : ℝ // 0 < a} := Subtype.borelSpace _
  have _bs2 : BorelSpace ({a : ℝ // 0 < a} × ℝ) := Prod.borelSpace
  exact continuous_mkOfCoefs.measurable

lemma AffineIncrEquiv.continuous_of_continuous_coefs {Z : Type*} [TopologicalSpace Z]
    {f : Z → AffineIncrEquiv} (f_fst_cont : Continuous fun z ↦ (f z).coefs.1)
    (f_snd_cont : Continuous fun z ↦ (f z).coefs.2) :
    Continuous f := by
  convert AffineIncrEquiv.continuous_mkOfCoefs.comp <|
    show Continuous fun z ↦ (⟨⟨(f z).coefs.1, (f z).isOrientationPreserving⟩, (f z).coefs.2⟩) by
      continuity
  ext z x
  simp

lemma AffineIncrEquiv.measurable_of_measurable_coefs {Z : Type*} [MeasurableSpace Z]
    {f : Z → AffineIncrEquiv} (f_fst_cont : Measurable fun z ↦ (f z).coefs.1)
    (f_snd_cont : Measurable fun z ↦ (f z).coefs.2) :
    Measurable f := by
  convert AffineIncrEquiv.measurable_mkOfCoefs.comp <|
    show Measurable fun z ↦ (⟨⟨(f z).coefs.1, (f z).isOrientationPreserving⟩, (f z).coefs.2⟩) by
      measurability
  ext z x
  simp

instance : MeasurableSpace (Multiplicative ℝ) := borel (Multiplicative ℝ)

instance : BorelSpace (Multiplicative ℝ) := ⟨rfl⟩

lemma measurable_toAdd :
    Measurable (fun (s : Multiplicative ℝ) ↦ s.toAdd) :=
  continuous_toAdd.measurable

lemma measurable_toMultiplicative :
    Measurable (fun (s : ℝ) ↦ Multiplicative.ofAdd s) :=
  continuous_ofAdd.measurable

/-- Characterization of homomorphisms `f : ℝ → AffineIncrEquiv`. -/
theorem AffineIncrEquiv.homomorphism_from_Real_characterization
    (f : MonoidHom (Multiplicative ℝ) AffineIncrEquiv) (f_mble : Measurable f) :
    (∃ β, f = homOfIndex₀ β) ∨ (∃ α c, f = homOfIndex α c) := by
  sorry -- TODO: Create issue.

/-- Characterization of nontrivial homomorphisms `f : ℝ → AffineIncrEquiv`. -/
theorem AffineIncrEquiv.homomorphism_from_Real_characterization_of_nontrivial
    {f : MonoidHom (Multiplicative ℝ) AffineIncrEquiv} (f_nontriv : ¬ f = 1)
    (f_mble : Measurable f) :
    (∃ β, β ≠ 0 ∧ f = homOfIndex₀ β) ∨ (∃ α c, α ≠ 0 ∧ f = homOfIndex α c) := by
  cases' homomorphism_from_Real_characterization f f_mble with h₀ h₁
  · obtain ⟨β, hβ⟩ := h₀
    refine Or.inl ⟨β, ?_, hβ⟩
    by_contra maybe_zero
    apply f_nontriv
    ext x
    simp [hβ, maybe_zero]
  · obtain ⟨α, c, h⟩ := h₁
    refine Or.inr ⟨α, c, ?_, h⟩
    by_contra maybe_zero
    apply f_nontriv
    ext x
    simp [h, maybe_zero]

end one_parameter_subgroups_of_affine_transformations
