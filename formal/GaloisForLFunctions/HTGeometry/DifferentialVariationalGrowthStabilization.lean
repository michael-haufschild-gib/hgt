import GaloisForLFunctions.HTGeometry.DifferentialVariationalBoundaryPair

/-!
# The variational growth filtration stabilizes

The attracting core was defined as an intersection over all rates.  This leaf proves that the
intersection is attained at a finite stage, so the core is *itself* a slow set and escape from it is
uniform.

The mechanism is a Noetherian/Artinian argument on subspaces.  A slow set is only a valuation-ring
submodule, but its **saturation** under uniformizer dilations,

```text
variationalSlowSaturation σ b L c = { v : ∃ z, π^z • v ∈ variationalSlowSet σ b L c }
```

is a subspace over the completed skew field: an arbitrary nonzero scalar factors as `π^{-t}` times a
valuation-ring element, and conjugating a valuation-ring element by a uniformizer power keeps it
integral (`DiffOp.uniformizer_conj_mem_integer`) because the valuation is multiplicative.  Two
inclusions sandwich the saturation between neighbouring slow sets,

```text
variationalSlowSet_subset_saturation          S c ⊆ Sat c
variationalSlowSaturation_subset_slowSet      Sat c ⊆ S (c-1)
```

the second because dilating by `π^{-z}` costs only a constant, which one rate step absorbs.  The
saturations therefore form a descending chain of subspaces of a finite-rank space, which stabilizes.
Sandwiching again turns that into stabilization of the slow sets themselves:

```text
exists_variationalSlowSet_eq_attractingCore
    ∃ c₀ ≥ 1, ∀ m ≥ c₀, variationalSlowSet σ b L m = variationalAttractingCore σ b L
exists_uniform_escape_rate
    ∃ c₀ ≥ 1, every vector outside the core escapes π^{-⌊n/c₀⌋} L infinitely often
```

Uniform escape is the quantitative separation the boundary pair needs: outside the attracting core
there is a single positive rate below which no vector stays.
-/

open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

omit [Algebra C K] [IsConstantBase C K] in
/-- The additive value of a uniformizer power. -/
theorem DiffOp.completedPseudoDiffOpAddValue_uniformizer_zpow (z : ℤ) :
    DiffOp.completedPseudoDiffOpAddValue
        ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ z :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) = (z : WithTop ℤ) := by
  rw [DiffOp.completedPseudoDiffOpAddValue_unit_eq_coe,
    DiffOp.completedPseudoDiffOpUnitAddValue_uniformizer_zpow]

omit [Algebra C K] [IsConstantBase C K] in
/-- Conjugation by a uniformizer power preserves the valuation ring. -/
theorem DiffOp.uniformizer_conj_mem_integer (z : ℤ)
    {o : DiffOp.CompletedPseudoDiffOp K} (ho : o ∈ DiffOp.CompletedPseudoDiffOpInteger (K := K)) :
    ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ z :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) * o *
      ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-z) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) ∈
      DiffOp.CompletedPseudoDiffOpInteger (K := K) := by
  rcases eq_or_ne o 0 with rfl | hne
  · simp
  · set u : (DiffOp.CompletedPseudoDiffOp K)ˣ := Units.mk0 o hne with hu
    have hval : (u : DiffOp.CompletedPseudoDiffOp K) = o := rfl
    have hnn : 0 ≤ DiffOp.completedPseudoDiffOpUnitAddValue u := by
      rw [DiffOp.mem_completedPseudoDiffOpInteger_iff_addValue_nonneg, ← hval,
        DiffOp.completedPseudoDiffOpAddValue_unit_eq_coe] at ho
      exact_mod_cast ho
    have hprod : ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ z :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) * o *
        ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-z) :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) =
        ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ z * u *
          DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-z) :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) := rfl
    rw [hprod, DiffOp.mem_completedPseudoDiffOpInteger_iff_addValue_nonneg,
      DiffOp.completedPseudoDiffOpAddValue_unit_eq_coe,
      DiffOp.completedPseudoDiffOpUnitAddValue_mul,
      DiffOp.completedPseudoDiffOpUnitAddValue_mul,
      DiffOp.completedPseudoDiffOpUnitAddValue_uniformizer_zpow,
      DiffOp.completedPseudoDiffOpUnitAddValue_uniformizer_zpow]
    have harith : z + DiffOp.completedPseudoDiffOpUnitAddValue u + (-z) =
        DiffOp.completedPseudoDiffOpUnitAddValue u := by ring
    rw [harith]
    exact_mod_cast hnn

/-- Slow sets shrink as the rate index grows. -/
theorem variationalSlowSet_antitone (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) {c c' : ℕ}
    (hc : 1 ≤ c) (hcc : c ≤ c') :
    variationalSlowSet σ b L c' ⊆ variationalSlowSet σ b L c := by
  intro v hv
  filter_upwards [hv] with n hn
  refine DiffOp.leftScale_uniformizer_zpow_carrier_antitone L ?_ hn
  have hdiv : n / c' ≤ n / c := Nat.div_le_div_left hcc hc
  omega

/-- Dilating by a uniformizer power moves a vector one rate index down. -/
theorem uniformizer_smul_mem_variationalSlowSet (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) {c : ℕ} (hc : 2 ≤ c) (z : ℕ)
    {v : Fin r → DiffOp.CompletedPseudoDiffOp K} (hv : v ∈ variationalSlowSet σ b L c) :
    ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(z : ℤ)) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • v ∈
      variationalSlowSet σ b L (c - 1) := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hv
  refine Filter.eventually_atTop.2 ⟨M + c * z * (c - 1) + c, fun n hn => ?_⟩
  have hbase := hM n (by omega)
  rw [(σ ^ n).vecBuildingAction_smul b,
    (σ ^ n).mapCompletedPseudoRingEquiv_uniformizer_zpow (-(z : ℤ))]
  have hscaled := DiffOp.smul_mem_leftScale
    (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(z : ℤ))) _ hbase
  rw [DiffOp.leftScaleCompletedPseudoDiffOpLattice_mul, ← zpow_add] at hscaled
  refine DiffOp.leftScale_uniformizer_zpow_carrier_antitone L ?_ hscaled
  have hq : (n / c) * c ≤ n := Nat.div_mul_le_self _ _
  have hid : (n / c) * (c - 1) + (n / c) = (n / c) * c := by
    cases c with
    | zero => omega
    | succ m =>
        simp only [Nat.succ_sub_one]
        have : (n / (m + 1)) * (m + 1) = (n / (m + 1)) * m + n / (m + 1) := by ring
        omega
  have hzc : z * (c - 1) ≤ n / c := by
    rw [Nat.le_div_iff_mul_le (show 0 < c by omega)]
    have hcomm : z * (c - 1) * c = c * z * (c - 1) := by ring
    omega
  have hkey : n / c + z ≤ n / (c - 1) := by
    rw [Nat.le_div_iff_mul_le (show 0 < c - 1 by omega)]
    have hdist : (n / c + z) * (c - 1) = (n / c) * (c - 1) + z * (c - 1) := by ring
    omega
  omega


omit [Algebra C K] [IsConstantBase C K] in
/-- Nonnegative uniformizer powers are integral. -/
theorem DiffOp.uniformizer_natPow_mem_integer (d : ℕ) :
    ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (d : ℤ) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) ∈
      DiffOp.CompletedPseudoDiffOpInteger (K := K) := by
  rw [DiffOp.mem_completedPseudoDiffOpInteger_iff_addValue_nonneg,
    DiffOp.completedPseudoDiffOpAddValue_uniformizer_zpow (K := K) (d : ℤ)]
  exact_mod_cast Int.natCast_nonneg d

omit [Algebra C K] [IsConstantBase C K] in
/-- Regrouping a uniformizer shift as an integral factor times a uniformizer power. -/
theorem DiffOp.uniformizer_shift_factorization (z d : ℕ) (t m : ℤ)
    (a : DiffOp.CompletedPseudoDiffOp K)
    (h : (d : ℤ) + ((z : ℤ) + t) = m) :
    ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ m :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) * a =
      (((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (d : ℤ) :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) *
        (((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (z : ℤ) :
            (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) *
          (((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ t :
              (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) * a) *
          ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(z : ℤ)) :
            (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K))) *
      ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (z : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) := by
  symm
  have hcancel :
      ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(z : ℤ)) :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) *
        ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (z : ℤ) :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) = 1 := by
    rw [← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one]
  have hcombine :
      ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (d : ℤ) :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) *
        (((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (z : ℤ) :
            (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) *
          ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ t :
            (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K)) =
      ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ m :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) := by
    rw [← Units.val_mul, ← Units.val_mul, ← zpow_add, ← zpow_add, h]
  calc
    (((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (d : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) *
      (((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (z : ℤ) :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) *
        (((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ t :
            (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) * a) *
        ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(z : ℤ)) :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K))) *
      ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (z : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K)
        = ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (d : ℤ) :
            (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) *
          (((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (z : ℤ) :
              (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) *
            (((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ t :
                (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) *
              (a * (((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(z : ℤ)) :
                (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) *
                ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (z : ℤ) :
                  (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K))))) := by
            simp only [mul_assoc]
      _ = ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (d : ℤ) :
            (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) *
          (((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (z : ℤ) :
              (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) *
            (((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ t :
                (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) * a)) := by
            rw [hcancel, mul_one]
      _ = (((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (d : ℤ) :
            (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) *
          (((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (z : ℤ) :
              (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) *
            ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ t :
              (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K))) * a := by
            simp only [mul_assoc]
      _ = ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ m :
            (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) * a := by
            rw [hcombine]


set_option synthInstance.maxHeartbeats 400000 in
/-- Vectors that some uniformizer power pushes into a slow set. -/
def variationalSlowSaturation (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) (c : ℕ) :
    Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K) where
  carrier := {v | ∃ z : ℕ,
    ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (z : ℤ) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • v ∈
      variationalSlowSet σ b L c}
  add_mem' := by
    rintro v w ⟨zv, hzv⟩ ⟨zw, hzw⟩
    have hsplit : ∀ (y : Fin r → DiffOp.CompletedPseudoDiffOp K) (e : ℕ),
        e ≤ max zv zw →
        ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (e : ℤ) :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • y ∈
          variationalSlowSet σ b L c →
        ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ ((max zv zw : ℕ) : ℤ) :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • y ∈
          variationalSlowSet σ b L c := by
      intro y e he hy
      have hfac : ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^
            ((max zv zw : ℕ) : ℤ) : (DiffOp.CompletedPseudoDiffOp K)ˣ) :
            DiffOp.CompletedPseudoDiffOp K) • y =
          ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ ((max zv zw - e : ℕ) : ℤ) :
            (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) •
            (((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (e : ℤ) :
              (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • y) := by
        rw [smul_smul, ← Units.val_mul, ← zpow_add]
        congr 3
        omega
      rw [hfac]
      exact (variationalSlowSubmodule σ b L c).smul_mem
        ⟨_, DiffOp.uniformizer_natPow_mem_integer (K := K) (max zv zw - e)⟩ hy
    refine ⟨max zv zw, ?_⟩
    rw [smul_add]
    exact (variationalSlowSubmodule σ b L c).add_mem
      (hsplit v zv (le_max_left _ _) hzv) (hsplit w zw (le_max_right _ _) hzw)
  zero_mem' := ⟨0, by
    rw [smul_zero]
    exact (variationalSlowSubmodule σ b L c).zero_mem⟩
  smul_mem' := by
    rintro a v ⟨z, hz⟩
    obtain ⟨t, ht⟩ := DiffOp.exists_uniformizer_left_scale_mem_integer a
    refine ⟨((z : ℤ) + t).toNat, ?_⟩
    set d : ℕ := (((((z : ℤ) + t).toNat : ℕ) : ℤ) - ((z : ℤ) + t)).toNat with hd
    have hsum : (d : ℤ) + ((z : ℤ) + t) = ((((z : ℤ) + t).toNat : ℕ) : ℤ) := by
      simp only [hd]
      omega
    rw [smul_smul, DiffOp.uniformizer_shift_factorization (K := K) z d t _ a hsum,
      ← smul_smul]
    refine (variationalSlowSubmodule σ b L c).smul_mem ⟨_, ?_⟩ hz
    exact mul_mem (DiffOp.uniformizer_natPow_mem_integer (K := K) d)
      (DiffOp.uniformizer_conj_mem_integer (K := K) (z : ℤ) ht)

@[simp] theorem mem_variationalSlowSaturation (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) (c : ℕ)
    (v : Fin r → DiffOp.CompletedPseudoDiffOp K) :
    v ∈ variationalSlowSaturation σ b L c ↔ ∃ z : ℕ,
      ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (z : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • v ∈
        variationalSlowSet σ b L c := Iff.rfl

/-- A slow set sits inside its saturation. -/
theorem variationalSlowSet_subset_saturation (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) (c : ℕ) :
    variationalSlowSet σ b L c ⊆ (variationalSlowSaturation σ b L c : Set _) := by
  intro v hv
  refine ⟨0, ?_⟩
  rw [Nat.cast_zero, zpow_zero, Units.val_one, one_smul]
  exact hv

/-- The saturation sits one rate index below. -/
theorem variationalSlowSaturation_subset_slowSet (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) {c : ℕ} (hc : 2 ≤ c) :
    (variationalSlowSaturation σ b L c : Set _) ⊆ variationalSlowSet σ b L (c - 1) := by
  rintro v ⟨z, hz⟩
  have hshift := uniformizer_smul_mem_variationalSlowSet σ b L hc z hz
  have hcancel : ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(z : ℤ)) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) •
      (((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (z : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • v) = v := by
    rw [smul_smul, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one,
      one_smul]
  rwa [hcancel] at hshift


/-- Saturations shrink as the rate index grows. -/
theorem variationalSlowSaturation_antitone (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) {c c' : ℕ}
    (hc : 1 ≤ c) (hcc : c ≤ c') :
    variationalSlowSaturation σ b L c' ≤ variationalSlowSaturation σ b L c := by
  rintro v ⟨z, hz⟩
  exact ⟨z, variationalSlowSet_antitone σ b L hc hcc hz⟩

/-- **The growth filtration stabilizes.**  Beyond a finite rate index the slow set no longer
shrinks, so the attracting core is reached at a finite stage. -/
theorem exists_variationalSlowSet_eq_attractingCore (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    ∃ c₀ : ℕ, 1 ≤ c₀ ∧ ∀ m, c₀ ≤ m →
      variationalSlowSet σ b L m = variationalAttractingCore σ b L := by
  classical
  let f : ℕ →o (Submodule (DiffOp.CompletedPseudoDiffOp K)
      (Fin r → DiffOp.CompletedPseudoDiffOp K))ᵒᵈ :=
    { toFun := fun k => OrderDual.toDual (variationalSlowSaturation σ b L (k + 1))
      monotone' := by
        intro k k' hkk
        exact OrderDual.toDual_le_toDual.2
          (variationalSlowSaturation_antitone σ b L (by omega) (by omega)) }
  obtain ⟨n₀, hn₀⟩ := IsArtinian.monotone_stabilizes f
  have hsat : ∀ m, n₀ + 1 ≤ m →
      variationalSlowSaturation σ b L m = variationalSlowSaturation σ b L (n₀ + 1) := by
    intro m hm
    have hthis := hn₀ (m - 1) (by omega)
    have hm1 : m - 1 + 1 = m := by omega
    have h2 : variationalSlowSaturation σ b L (n₀ + 1) =
        variationalSlowSaturation σ b L (m - 1 + 1) := hthis
    rw [hm1] at h2
    exact h2.symm
  have hstable : ∀ m, n₀ + 2 ≤ m →
      variationalSlowSet σ b L m =
        (variationalSlowSaturation σ b L (n₀ + 1) : Set _) := by
    intro m hm
    apply Set.Subset.antisymm
    · rw [← hsat m (by omega)]
      exact variationalSlowSet_subset_saturation σ b L m
    · rw [← hsat (m + 1) (by omega)]
      have := variationalSlowSaturation_subset_slowSet σ b L
        (c := m + 1) (by omega)
      simpa using this
  refine ⟨n₀ + 2, by omega, fun m hm => ?_⟩
  rw [hstable m hm]
  apply Set.Subset.antisymm
  · intro v hv
    rw [variationalAttractingCore, Set.mem_iInter]
    intro c
    rcases le_or_gt (n₀ + 2) (c + 1) with hc | hc
    · rw [hstable (c + 1) hc]
      exact hv
    · refine variationalSlowSet_antitone σ b L (by omega) (show c + 1 ≤ n₀ + 2 by omega) ?_
      rw [hstable (n₀ + 2) (by omega)]
      exact hv
  · intro v hv
    have := Set.mem_iInter.1 hv (n₀ + 1)
    rw [show n₀ + 1 + 1 = n₀ + 2 from rfl] at this
    rw [← hstable (n₀ + 2) (by omega)]
    exact this

/-- **Uniform escape.**  Outside the attracting core every vector leaves the base lattice at a
rate bounded below by a single positive constant. -/
theorem exists_uniform_escape_rate (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    ∃ c₀ : ℕ, 1 ≤ c₀ ∧ ∀ v : Fin r → DiffOp.CompletedPseudoDiffOp K,
      v ∉ variationalAttractingCore σ b L →
        ∃ᶠ n : ℕ in Filter.atTop,
          (σ ^ n).vecBuildingAction b v ∉
            (DiffOp.leftScaleCompletedPseudoDiffOpLattice
              (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^
                (-((n / c₀ : ℕ) : ℤ))) L).carrier := by
  obtain ⟨c₀, hc₀, hstab⟩ := exists_variationalSlowSet_eq_attractingCore σ b L
  refine ⟨c₀, hc₀, fun v hv => ?_⟩
  have hnot : v ∉ variationalSlowSet σ b L c₀ := by
    rw [hstab c₀ le_rfl]
    exact hv
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  apply hnot
  filter_upwards [hcon] with n hn
  exact not_not.1 hn

end

end GaloisForLFunctions.HTGeometry
