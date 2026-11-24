import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TracedLaurentResidue

/-! Coefficients of regular top forms in the logarithmic volume
form a rank-one lattice on every nonempty coordinate intersection. -/

noncomputable section

open GlobalTheory.CechDR
open scoped GlobalTheory.CechDR

namespace GlobalTheory.PD

variable {k F : Type} [Field k] [Field F] [Algebra k F]
  {d : ℕ} {x : Fin (d + 1) → F}

/-- The change from logarithmic coefficients to the affine chart's volume. -/
def logCoefficientScale (x : Fin (d + 1) → F) (i : Fin (d + 1)) : F := ∏ l, x i / x l

/-- Regularity of a logarithmic coefficient is regularity in every
available affine volume. -/
def logCoefficientLattice (k : Type) [Field k] [Algebra k F]
    (x : Fin (d + 1) → F) (I : Finset (Fin (d + 1))) : Submodule k F :=
  ⨅ i : I, (rA k x I).toSubmodule.comap (LinearMap.mul k F (logCoefficientScale x i))

theorem mem_logCoefficientLattice_iff {I : Finset (Fin (d + 1))} {c : F} :
    c ∈ logCoefficientLattice k x I ↔
      ∀ i ∈ I, logCoefficientScale x i * c ∈ rA k x I := by
  rw [logCoefficientLattice, Submodule.mem_iInf]
  exact ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i i.property⟩

private theorem logCoefficientScale_change (h : IsPd k x) (i j : Fin (d + 1)) :
    logCoefficientScale x j = (x j / x i) ^ (d + 1) * logCoefficientScale x i := by
  have hp : (∏ _ : Fin (d + 1), x j / x i) = (x j / x i) ^ (d + 1) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [logCoefficientScale]
  rw [← hp, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [div_mul_div_cancel₀ (h.ne i)]

/-- Any chart in the intersection suffices to test a logarithmic coefficient. -/
theorem IsPd.mem_logCoefficientLattice_iff (h : IsPd k x) {I : Finset (Fin (d + 1))}
    {i : Fin (d + 1)} (hi : i ∈ I) {c : F} :
    c ∈ logCoefficientLattice k x I ↔ logCoefficientScale x i * c ∈ rA k x I := by
  rw [GlobalTheory.PD.mem_logCoefficientLattice_iff]
  refine ⟨fun h' => h' i hi, fun hc j _ => ?_⟩
  rw [logCoefficientScale_change h i j, mul_assoc]
  have hr : x j / x i ∈ rA k x I := Algebra.subset_adjoin ⟨i, hi, j, rfl⟩
  exact (rA k x I).mul_mem ((rA k x I).pow_mem hr (d + 1)) hc

/-- Restriction of regular top scalar coefficients to a smaller open. -/
theorem IsPd.logCoefficientLattice_mono (h : IsPd k x)
    {I J : Finset (Fin (d + 1))} (hI : I.Nonempty) (hIJ : I ⊆ J) :
    logCoefficientLattice k x I ≤ logCoefficientLattice k x J := by
  obtain ⟨i, hi⟩ := hI
  intro c hc
  exact (h.mem_logCoefficientLattice_iff (hIJ hi)).mpr
    (rA_mono hIJ ((h.mem_logCoefficientLattice_iff hi).mp hc))

/-- Multiplication by a regular chart scalar preserves the logarithmic
coefficient lattice. -/
theorem IsPd.smul_mem_logCoefficientLattice (h : IsPd k x)
    {I : Finset (Fin (d + 1))} (hI : I.Nonempty)
    {s c : F} (hs : s ∈ rA k x I) (hc : c ∈ logCoefficientLattice k x I) :
    s • c ∈ logCoefficientLattice k x I := by
  obtain ⟨i, hi⟩ := hI
  apply (h.mem_logCoefficientLattice_iff hi).mpr
  rw [smul_eq_mul, mul_left_comm]
  exact (rA k x I).mul_mem hs ((h.mem_logCoefficientLattice_iff hi).mp hc)

/-- The affine volume and its coefficient functional give a dual family
of length one for the lattice of logarithmic coefficients. -/
theorem IsPd.exists_logCoefficientLattice_dual (h : IsPd k x)
    {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) :
    ∃ (v : F) (φ : F →ₗ[F] F), v ∈ logCoefficientLattice k x I ∧
      (∀ c ∈ logCoefficientLattice k x I, φ c ∈ rA k x I) ∧ ∀ c, c = φ c • v := by
  let u := logCoefficientScale x i
  have hu : u ≠ 0 := Finset.prod_ne_zero_iff.mpr fun l _ => div_ne_zero (h.ne i) (h.ne l)
  refine ⟨u⁻¹, LinearMap.mul F F u, ?_, fun _ hc => (h.mem_logCoefficientLattice_iff hi).mp hc, ?_⟩
  · apply (h.mem_logCoefficientLattice_iff hi).mpr
    change u * u⁻¹ ∈ rA k x I
    rw [mul_inv_cancel₀ hu]
    exact one_mem _
  · intro c
    change c = (u * c) * u⁻¹
    rw [mul_right_comm, mul_inv_cancel₀ hu, one_mul]

variable {E : Type} [CharZero k] [Field E] [Algebra k E] [Algebra F E] [IsScalarTower k F E]

/-- The field trace of the logarithmic coefficient of a regular top
form belongs to the corresponding scalar lattice. -/
theorem IsFinCover.trace_logarithmic_coefficient_mem_lattice
    (h : IsFinCover k E x) (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ)
    {I : Finset (Fin (d + 1))} (w : DR k E) (hw : w ∈ omB k E (rB k E x I) d) :
    Algebra.trace F E (τ w) ∈ logCoefficientLattice k x I :=
  mem_logCoefficientLattice_iff.mpr fun _ hi =>
    h.trace_logarithmic_coefficient_mem_chart τ hτ hi w hw

end GlobalTheory.PD
