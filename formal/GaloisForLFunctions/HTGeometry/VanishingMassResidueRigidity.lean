import GaloisForLFunctions.HTGeometry.UniversalPrimeOrientationLimit
import GaloisForLFunctions.HTGeometry.PrimeDirichletTailPattern

/-!
# Vanishing-mass finite-residue projective rigidity

A signed simple-pole palette whose nonzero masses vanish asymptotically cannot absorb a
finite-range residue correction.  Any constant affine residue action preserving the palette is
eventually the identity or the global sign reversal.  The terminal theorem instantiates this law
on the actual summable universal prime-log residue masses.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Set
open scoped Topology

noncomputable section

/-- A finite-range function into a `T₁` space which converges to zero is eventually zero. -/
theorem eventually_eq_zero_of_finite_range_tendsto_zero
    {P R : Type*} [TopologicalSpace R] [T1Space R] [Zero R]
    {l : Filter P} (q : P → R) (hfinite : (Set.range q).Finite)
    (hq : Tendsto q l (nhds 0)) :
    ∀ᶠ p in l, q p = 0 := by
  let bad : Set R := Set.range q \ {0}
  have hbadfinite : bad.Finite := by
    exact hfinite.sdiff
  have hbad : IsClosed bad := hbadfinite.isClosed
  have hzero : 0 ∈ badᶜ := by simp [bad]
  have hnhds : badᶜ ∈ nhds 0 := hbad.isOpen_compl.mem_nhds hzero
  filter_upwards [hq.eventually hnhds] with p hp
  by_contra hp0
  exact hp ⟨Set.mem_range_self p, hp0⟩

@[simp] theorem norm_primeDirichletRealSign (b : Bool) :
    ‖primeDirichletRealSign b‖ = 1 := by
  cases b <;> simp [primeDirichletRealSign]

theorem scalar_of_boolean_sign_relation
    (a : ℝ) (x y : Bool)
    (h : primeDirichletRealSign y = a * primeDirichletRealSign x) :
    a = 1 ∨ a = -1 := by
  cases x <;> cases y
  · left
    simpa [primeDirichletRealSign] using h.symm
  · right
    simpa [primeDirichletRealSign] using h.symm
  · right
    simp [primeDirichletRealSign] at h
    linarith
  · left
    simp [primeDirichletRealSign] at h
    linarith

theorem primeDirichletRealSign_injective :
    Function.Injective primeDirichletRealSign := by
  intro x y h
  cases x <;> cases y
  · rfl
  · norm_num [primeDirichletRealSign] at h
  · norm_num [primeDirichletRealSign] at h
  · rfl

theorem primeDirichletRealSign_eq_neg_iff_ne (x y : Bool) :
    primeDirichletRealSign y = -primeDirichletRealSign x ↔ x ≠ y := by
  cases x <;> cases y <;> norm_num [primeDirichletRealSign]

/-- A vanishing signed mass palette screens every finite-range additive residue correction.
Only the two global projective scalars survive. -/
theorem vanishingMass_finiteResidueCorrection_projective
    {P : Type*} {l : Filter P} [l.NeBot]
    (epsilon delta : P → Bool) (w q : P → ℝ) (a : ℝ)
    (hw : Tendsto w l (nhds 0))
    (hwne : ∀ᶠ p in l, w p ≠ 0)
    (hqfinite : (Set.range q).Finite)
    (hresidue : ∀ᶠ p in l,
      primeDirichletRealSign (delta p) * w p =
        a * (primeDirichletRealSign (epsilon p) * w p) + q p) :
    (a = 1 ∧ ∀ᶠ p in l, epsilon p = delta p) ∨
      (a = -1 ∧ ∀ᶠ p in l, epsilon p ≠ delta p) := by
  let c : P → ℝ := fun p =>
    primeDirichletRealSign (delta p) -
      a * primeDirichletRealSign (epsilon p)
  have hcbound : ∀ p, ‖c p‖ ≤ 1 + ‖a‖ := by
    intro p
    calc
      ‖c p‖ ≤ ‖primeDirichletRealSign (delta p)‖ +
          ‖a * primeDirichletRealSign (epsilon p)‖ := norm_sub_le _ _
      _ = 1 + ‖a‖ := by
        rw [norm_mul, norm_primeDirichletRealSign,
          norm_primeDirichletRealSign, mul_one]
  have hcbounded :
      IsBoundedUnder (· ≤ ·) l (norm ∘ c) :=
    isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall fun p => hcbound p)
  have hcwmul : Tendsto (fun p => c p * w p) l (nhds 0) :=
    Filter.isBoundedUnder_le_mul_tendsto_zero hcbounded hw
  have hqeq : ∀ᶠ p in l, q p = c p * w p := by
    filter_upwards [hresidue] with p hp
    dsimp [c]
    linear_combination -hp
  have hqzero : ∀ᶠ p in l, q p = 0 :=
    eventually_eq_zero_of_finite_range_tendsto_zero q hqfinite
      (hcwmul.congr' (hqeq.mono fun _ hp => hp.symm))
  have hsign : ∀ᶠ p in l,
      primeDirichletRealSign (delta p) =
        a * primeDirichletRealSign (epsilon p) := by
    filter_upwards [hresidue, hqzero, hwne] with p hp hqp hwp
    rw [hqp, add_zero] at hp
    apply mul_right_cancel₀ hwp
    calc
      primeDirichletRealSign (delta p) * w p =
          a * (primeDirichletRealSign (epsilon p) * w p) := hp
      _ = (a * primeDirichletRealSign (epsilon p)) * w p := by ring
  obtain ⟨p, hp⟩ := hsign.exists
  rcases scalar_of_boolean_sign_relation a (epsilon p) (delta p) hp with ha | ha
  · left
    refine ⟨ha, ?_⟩
    filter_upwards [hsign] with r hr
    rw [ha, one_mul] at hr
    exact primeDirichletRealSign_injective hr.symm
  · right
    refine ⟨ha, ?_⟩
    filter_upwards [hsign] with r hr
    rw [ha] at hr
    exact (primeDirichletRealSign_eq_neg_iff_ne (epsilon r) (delta r)).mp (by
      simpa only [neg_mul, one_mul] using hr)

/-- The actual universal prime-log masses vanish on the cofinite prime filter. -/
theorem tendsto_universalPrimeWeight_cofinite :
    Tendsto universalPrimeWeight cofinite (nhds 0) := by
  have hsum : Summable universalPrimeWeight := by
    apply Summable.of_norm
    simpa [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (universalPrimeWeight_pos _)] using
      summable_norm_universalPrimeWeight
  exact hsum.tendsto_cofinite_zero

/-- A finite family of quantized pole-order corrections. -/
def finiteQuantizedResidueCorrection
    {J P : Type*} [Fintype J]
    (coefficient : J → ℝ) (order : J → P → ℤ) (p : P) : ℝ :=
  ∑ j, coefficient j * order j p

/-- Bounded quantized pole orders produce a finite residue-correction palette. -/
theorem finite_range_finiteQuantizedResidueCorrection
    {J P : Type*} [Fintype J]
    (coefficient : J → ℝ) (order : J → P → ℤ)
    (horder : ∀ j, (Set.range (order j)).Finite) :
    (Set.range (finiteQuantizedResidueCorrection coefficient order)).Finite := by
  classical
  let pattern : P → J → ℤ := fun p j => order j p
  let evaluate : (J → ℤ) → ℝ := fun x => ∑ j, coefficient j * x j
  have hpatterns : (Set.range pattern).Finite := by
    apply (Set.Finite.pi' horder).subset
    rintro x ⟨p, rfl⟩ j
    exact Set.mem_range_self p
  apply (hpatterns.image evaluate).subset
  rintro x ⟨p, rfl⟩
  exact ⟨pattern p, Set.mem_range_self p, rfl⟩

/-- For the actual universal prime-log residue masses, an affine residue transformation with a
finite correction palette is eventually the identity or the global sign reversal. -/
theorem universalPrimeWeight_finiteResidueCorrection_projective
    (epsilon delta : Nat.Primes → Bool) (q : Nat.Primes → ℝ) (a : ℝ)
    (hqfinite : (Set.range q).Finite)
    (hresidue : ∀ᶠ p in cofinite,
      primeDirichletRealSign (delta p) * universalPrimeWeight p =
        a * (primeDirichletRealSign (epsilon p) * universalPrimeWeight p) + q p) :
    (a = 1 ∧ PrimeOrientationsEventuallyEqual epsilon delta) ∨
      (a = -1 ∧ PrimeOrientationsEventuallyOpposite epsilon delta) := by
  have h := vanishingMass_finiteResidueCorrection_projective
    epsilon delta universalPrimeWeight q a
    tendsto_universalPrimeWeight_cofinite
    (Filter.Eventually.of_forall fun p => (universalPrimeWeight_pos p).ne')
    hqfinite hresidue
  simpa [PrimeOrientationsEventuallyEqual, PrimeOrientationsEventuallyOpposite,
    Filter.eventually_cofinite] using h

/-- Prime specialization for a finite family of bounded quantized residue corrections. -/
theorem universalPrimeWeight_finiteQuantizedResidueCorrection_projective
    {J : Type*} [Fintype J]
    (epsilon delta : Nat.Primes → Bool) (a : ℝ)
    (coefficient : J → ℝ) (order : J → Nat.Primes → ℤ)
    (horder : ∀ j, (Set.range (order j)).Finite)
    (hresidue : ∀ᶠ p in cofinite,
      primeDirichletRealSign (delta p) * universalPrimeWeight p =
        a * (primeDirichletRealSign (epsilon p) * universalPrimeWeight p) +
          finiteQuantizedResidueCorrection coefficient order p) :
    (a = 1 ∧ PrimeOrientationsEventuallyEqual epsilon delta) ∨
      (a = -1 ∧ PrimeOrientationsEventuallyOpposite epsilon delta) := by
  exact universalPrimeWeight_finiteResidueCorrection_projective epsilon delta
    (finiteQuantizedResidueCorrection coefficient order) a
    (finite_range_finiteQuantizedResidueCorrection coefficient order horder) hresidue

end

end GaloisForLFunctions.HTGeometry
