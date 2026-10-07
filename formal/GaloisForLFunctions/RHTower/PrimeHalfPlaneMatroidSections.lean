import GaloisForLFunctions.RHTower.PrimeCayleyHalfPlane
import GaloisForLFunctions.HTGeometry.HurwitzClosedZeroLocus
import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# Half-plane-property polynomials at the prime Cayley fields

Let `B` be a homogeneous polynomial of degree `r` in finitely many variables with the
half-plane property: `B(x) ≠ 0` whenever every `Re xᵢ > 0`.  Label the variables by primes `ℓ(i)` and
evaluate at the Cayley coordinates `xᵢ(z) = (1 + uᵢ)/(1 − uᵢ)` of the centered prime fields
`uᵢ(z) = e^{−i z log ℓ(i)}`.

* Below the centered real axis every `uᵢ` lies in the unit disk, so every `xᵢ` has positive real part.
* Above it every `uᵢ` lies outside the disk, so every `xᵢ` has negative real part, and homogeneity
  gives `B(x) = (−1)^r B(−x)`.

Hence `B(x(z)) ≠ 0` off the real axis (`eval_primeCayley_ne_zero`).  Clearing denominators gives the
entire section

`F(z) = Σ_d c_d ∏ᵢ (1 + uᵢ)^{dᵢ} (1 − uᵢ)^{r − dᵢ}`  (`clearedSection`),

which equals `∏ᵢ (1 − uᵢ)^r · B(x(z))` off the axis.  It is entire, and all its zeros are real
(`clearedSection_im_eq_zero_of_eq_zero`).

**Receiver** (`riemannHypothesis_of_tendsto_clearedSection`).  If cleared sections of homogeneous
half-plane-property polynomials, each multiplied by an entire zero-free normalizer, converge locally
uniformly on `ℂ` to `E · XiC` with `E` entire and zero-free, then the Riemann hypothesis holds
(Hurwitz).  Normalizers are needed: a raw section carries the oscillating factor `∏ᵢ uᵢ^{r/2}`,
whose frequency `(r/2) Σᵢ log ℓ(i)` grows along any cofinal family.
-/

open Complex Filter Topology MvPolynomial

namespace RHTower.PrimeHalfPlaneMatroid

noncomputable section

variable {σ : Type*}

/-- The half-plane property: no zero when every variable has positive real part. -/
def HasHalfPlaneProperty (B : MvPolynomial σ ℂ) : Prop :=
  ∀ x : σ → ℂ, (∀ i, 0 < (x i).re) → eval x B ≠ 0

/-- Homogeneous scaling: `B(c x) = c^r B(x)`. -/
theorem eval_smul_of_isHomogeneous [Fintype σ] {B : MvPolynomial σ ℂ} {r : ℕ}
    (hB : B.IsHomogeneous r) (c : ℂ) (x : σ → ℂ) :
    eval (fun i => c * x i) B = c ^ r * eval x B := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : r = ∑ i ∈ d.support, d i := hB.degree_eq_sum_deg_support hd
  have hprod : ∏ i, (c * x i) ^ d i = c ^ (∑ i, d i) * ∏ i, x i ^ d i := by
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hsum : ∑ i, d i = r := by
    rw [hdeg]
    exact (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
      simpa using hi).symm
  rw [hprod, hsum]
  ring

/-- Homogeneous half-plane polynomials do not vanish on the common left half-plane. -/
theorem eval_ne_zero_of_re_neg [Fintype σ] {B : MvPolynomial σ ℂ} {r : ℕ}
    (hHPP : HasHalfPlaneProperty B) (hB : B.IsHomogeneous r) {x : σ → ℂ}
    (hx : ∀ i, (x i).re < 0) : eval x B ≠ 0 := by
  have hneg := hHPP (fun i => -x i) fun i => by simpa using hx i
  have hscale := eval_smul_of_isHomogeneous hB (-1) (fun i => -x i)
  simp only [neg_mul, one_mul, neg_neg] at hscale
  rw [hscale]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hneg

/-- **No off-axis zeros at the prime Cayley fields.** -/
theorem eval_primeCayley_ne_zero [Fintype σ] {B : MvPolynomial σ ℂ} {r : ℕ}
    (hHPP : HasHalfPlaneProperty B) (hB : B.IsHomogeneous r) (ℓ : σ → Nat.Primes) {z : ℂ}
    (hz : z.im ≠ 0) : eval (fun i => centeredPrimeCayley (ℓ i) z) B ≠ 0 := by
  rcases lt_or_gt_of_ne hz with hlt | hgt
  · exact hHPP _ fun i => centeredPrimeCayley_re_pos_of_im_lt_zero (ℓ i) hlt
  · exact eval_ne_zero_of_re_neg hHPP hB fun i => centeredPrimeCayley_re_neg_of_im_pos (ℓ i) hgt

/-! ## The denominator-cleared entire section -/

/-- `F(z) = Σ_d c_d ∏ᵢ (1 + uᵢ)^{dᵢ} (1 − uᵢ)^{r − dᵢ}`. -/
def clearedSection [Fintype σ] (B : MvPolynomial σ ℂ) (r : ℕ) (ℓ : σ → Nat.Primes) (z : ℂ) : ℂ :=
  ∑ d ∈ B.support, B.coeff d *
    ∏ i, (1 + centeredPrimeLeeYangField (ℓ i) z) ^ d i *
      (1 - centeredPrimeLeeYangField (ℓ i) z) ^ (r - d i)

theorem differentiable_centeredPrimeLeeYangField (p : Nat.Primes) :
    Differentiable ℂ (centeredPrimeLeeYangField p) := by
  unfold centeredPrimeLeeYangField centeredPrimeMark
  fun_prop

/-- The cleared section is entire. -/
theorem differentiable_clearedSection [Fintype σ] (B : MvPolynomial σ ℂ) (r : ℕ)
    (ℓ : σ → Nat.Primes) : Differentiable ℂ (clearedSection B r ℓ) := by
  unfold clearedSection
  have hu := fun i => differentiable_centeredPrimeLeeYangField (ℓ i)
  fun_prop

/-- Off the axis the cleared section is the cleared evaluation. -/
theorem clearedSection_eq [Fintype σ] {B : MvPolynomial σ ℂ} {r : ℕ} (hB : B.IsHomogeneous r)
    (ℓ : σ → Nat.Primes) {z : ℂ} (hz : z.im ≠ 0) :
    clearedSection B r ℓ z =
      (∏ i, (1 - centeredPrimeLeeYangField (ℓ i) z) ^ r) *
        eval (fun i => centeredPrimeCayley (ℓ i) z) B := by
  rw [clearedSection, eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hle : ∀ i, d i ≤ r := by
    intro i
    rw [hB.degree_eq_sum_deg_support hd]
    by_cases hi : i ∈ d.support
    · exact Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) hi
    · rw [Finsupp.notMem_support_iff.mp hi]
      exact Nat.zero_le _
  have hfac : ∀ i, (1 + centeredPrimeLeeYangField (ℓ i) z) ^ d i *
      (1 - centeredPrimeLeeYangField (ℓ i) z) ^ (r - d i) =
      (1 - centeredPrimeLeeYangField (ℓ i) z) ^ r * centeredPrimeCayley (ℓ i) z ^ d i := by
    intro i
    have hden := centeredPrimeCayley_denominator_ne_zero_of_im_ne_zero (ℓ i) hz
    rw [centeredPrimeCayley, diskToRight, div_pow]
    have hsplit : (1 - centeredPrimeLeeYangField (ℓ i) z) ^ r =
        (1 - centeredPrimeLeeYangField (ℓ i) z) ^ (r - d i) *
          (1 - centeredPrimeLeeYangField (ℓ i) z) ^ d i := by
      rw [← pow_add, Nat.sub_add_cancel (hle i)]
    rw [hsplit]
    field_simp
  rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_mul_distrib]
  ring

/-- **All zeros of the cleared section are real.** -/
theorem clearedSection_im_eq_zero_of_eq_zero [Fintype σ] {B : MvPolynomial σ ℂ} {r : ℕ}
    (hHPP : HasHalfPlaneProperty B) (hB : B.IsHomogeneous r) (ℓ : σ → Nat.Primes) {z : ℂ}
    (hzero : clearedSection B r ℓ z = 0) : z.im = 0 := by
  by_contra hz
  rw [clearedSection_eq hB ℓ hz] at hzero
  rcases mul_eq_zero.mp hzero with h | h
  · rw [Finset.prod_eq_zero_iff] at h
    obtain ⟨i, -, hi⟩ := h
    exact centeredPrimeCayley_denominator_ne_zero_of_im_ne_zero (ℓ i) hz (pow_eq_zero_iff'.mp hi).1
  · exact eval_primeCayley_ne_zero hHPP hB ℓ hz h

/-! ## The Hurwitz receiver -/

/-- A finite half-plane-property datum: variables, prime labels, a homogeneous polynomial with the
half-plane property, and an entire normalizer without zeros.  The normalizer absorbs the oscillating
monomial `∏ᵢ uᵢ^{r/2}` that separates a cleared section from its symmetric form. -/
structure HPPSectionDatum where
  ι : Type
  [fintype : Fintype ι]
  label : ι → Nat.Primes
  poly : MvPolynomial ι ℂ
  degree : ℕ
  homogeneous : poly.IsHomogeneous degree
  halfPlane : HasHalfPlaneProperty poly
  normalizer : ℂ → ℂ
  normalizer_differentiable : Differentiable ℂ normalizer
  normalizer_ne_zero : ∀ z, normalizer z ≠ 0

attribute [instance] HPPSectionDatum.fintype

/-- The normalized cleared section of a datum. -/
def HPPSectionDatum.section (D : HPPSectionDatum) (z : ℂ) : ℂ :=
  D.normalizer z * clearedSection D.poly D.degree D.label z

theorem HPPSectionDatum.im_eq_zero_of_section_eq_zero (D : HPPSectionDatum)
    {z : ℂ} (h : D.section z = 0) : z.im = 0 :=
  clearedSection_im_eq_zero_of_eq_zero D.halfPlane D.homogeneous D.label
    ((mul_eq_zero.mp h).resolve_left (D.normalizer_ne_zero z))

theorem HPPSectionDatum.differentiable_section (D : HPPSectionDatum) :
    Differentiable ℂ D.section :=
  D.normalizer_differentiable.mul (differentiable_clearedSection _ _ _)

/-- **Receiver.**  If cleared sections of homogeneous half-plane-property polynomials at the prime
Cayley fields, times entire zero-free normalizers, converge locally uniformly on `ℂ` to `E · XiC`,
with `E` entire and zero-free, then the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_tendsto_clearedSection (D : ℕ → HPPSectionDatum)
    {E : ℂ → ℂ} (hE : Differentiable ℂ E) (hEne : ∀ z, E z ≠ 0)
    (hconv : TendstoLocallyUniformly (fun n => (D n).section) (fun z => E z * XiC z) atTop) :
    RiemannHypothesis := by
  have hlimit : AnalyticOnNhd ℂ (fun z => E z * XiC z) Set.univ := fun z _ =>
    (hE.analyticAt z).mul (XiC_analytic z (Set.mem_univ z))
  have h0 : E 0 * XiC 0 ≠ 0 := mul_ne_zero (hEne 0) XiC_zero_ne
  have hS : IsClosed {w : ℂ | w.im = 0} := isClosed_eq Complex.continuous_im continuous_const
  have hzeroS : ∀ᶠ n in atTop, ∀ w, (D n).section w = 0 → w ∈ {w : ℂ | w.im = 0} :=
    Eventually.of_forall fun n w hw => (D n).im_eq_zero_of_section_eq_zero hw
  have hdiff : ∀ᶠ n in atTop, Differentiable ℂ (D n).section :=
    Eventually.of_forall fun n => (D n).differentiable_section
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hρ hzero
  set z : ℂ := (ρ - 1 / 2) * (-I) with hz_def
  have hXiC : XiC z = 0 := by
    rw [XiC]
    have harg : (1 : ℂ) / 2 + z * I = ρ := by
      rw [hz_def, mul_assoc]
      have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
      rw [hI, mul_one]
      ring
    rw [harg, hzero]
  have hzIm : z.im = 1 / 2 - ρ.re := by simp [hz_def]
  have hzS : z ∈ {w : ℂ | w.im = 0} :=
    GaloisForLFunctions.HTGeometry.zero_mem_closed_of_tendstoLocallyUniformly hconv hlimit hdiff
      hS hzeroS h0 (by simp [hXiC])
  have hρh : 1 / 2 < ρ.re := mem_rightHalf.mp hρ
  simp only [Set.mem_setOf_eq] at hzS
  linarith

end

end RHTower.PrimeHalfPlaneMatroid
