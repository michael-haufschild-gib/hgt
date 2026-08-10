import GaloisForLFunctions.RHTower.EulerFisherCurvature
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix

/-!
# The prime-coordinate modular current is a holomorphic `ℓ²` field on `Re s > 1/2`

The squarefree Euler clock has one modular current per prime,

```text
j(s)_p = (log p) p^{-s} / (1 + p^{-s}).
```

On every open half-plane `Re s > b` with `b > 1/2` the denominators are uniformly bounded away
from zero, so the coefficients obey `‖j(s)_p‖ ≤ 4 (log p) p^{-b}` and are square-summable.  The
resulting vector field into `ℓ²(Primes)` is the locally uniform limit of its finite prime sections,
hence holomorphic throughout `Re s > 1/2`: no prime coordinate has a pole there.  The centered local
modular character `Δ_p(s) = p^{1/2 - s}` obeys the exact reflection law `Δ_p(1 - s) = Δ_p(s)⁻¹`.
-/

open Complex Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower

/-- The prime-coordinate modular current `j(s)_p = (log p) p^{-s}/(1 + p^{-s})`. -/
def coronaPrimeCurrentCoeff (s : ℂ) (p : Nat.Primes) : ℂ :=
  (Real.log ((p : ℕ) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-s) / (1 + ((p : ℕ) : ℂ) ^ (-s))

/-- The centered local modular character `Δ_p(s) = p^{1/2 - s}`. -/
def coronaLocalModularCharacter (s : ℂ) (p : Nat.Primes) : ℂ :=
  ((p : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)

/-- **Reflection law of the local modular character.**  `Δ_p(1 - s) = Δ_p(s)⁻¹`. -/
theorem coronaLocalModularCharacter_reflection (s : ℂ) (p : Nat.Primes) :
    coronaLocalModularCharacter (1 - s) p = (coronaLocalModularCharacter s p)⁻¹ := by
  rw [coronaLocalModularCharacter, coronaLocalModularCharacter, ← Complex.cpow_neg]
  congr 1
  ring

/-! ## Uniform coefficient bounds -/

theorem norm_primeCpowNeg (s : ℂ) (p : Nat.Primes) :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s.re) := by
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos, Complex.neg_re]

private theorem two_rpow_neg_half_le : (2 : ℝ) ^ (-(1 / 2) : ℝ) ≤ 3 / 4 := by
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hge : (4 : ℝ) / 3 ≤ Real.sqrt 2 := by nlinarith
  rw [Real.rpow_neg (by norm_num), ← Real.rpow_natCast (Real.sqrt 2) 2] at *
  rw [show ((1 : ℝ) / 2) = (1 / 2 : ℝ) from rfl, ← Real.sqrt_eq_rpow]
  rw [inv_le_iff_one_le_mul₀ hpos]
  nlinarith

theorem norm_primeCpowNeg_le {s : ℂ} (hs : 1 / 2 ≤ s.re) (p : Nat.Primes) :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 3 / 4 := by
  rw [norm_primeCpowNeg]
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  have h1 : ((p : ℕ) : ℝ) ^ (-s.re) ≤ ((p : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : ((p : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) := by
    rw [Real.rpow_neg hp0.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    apply inv_anti₀ (by positivity)
    exact Real.rpow_le_rpow (by norm_num) hp2 (by norm_num)
  have h3 := two_rpow_neg_half_le
  linarith

/-- On the closed half-plane `Re s ≥ 1/2` the Euler denominators are bounded below by `1/4`. -/
theorem norm_one_add_primeCpowNeg_ge {s : ℂ} (hs : 1 / 2 ≤ s.re) (p : Nat.Primes) :
    (1 : ℝ) / 4 ≤ ‖1 + ((p : ℕ) : ℂ) ^ (-s)‖ := by
  have hle := norm_primeCpowNeg_le hs p
  have htri : ‖(1 : ℂ)‖ ≤ ‖1 + ((p : ℕ) : ℂ) ^ (-s)‖ + ‖((p : ℕ) : ℂ) ^ (-s)‖ := by
    have h : (1 : ℂ) = (1 + ((p : ℕ) : ℂ) ^ (-s)) - ((p : ℕ) : ℂ) ^ (-s) := by ring
    calc ‖(1 : ℂ)‖ = ‖(1 + ((p : ℕ) : ℂ) ^ (-s)) - ((p : ℕ) : ℂ) ^ (-s)‖ := by rw [← h]
      _ ≤ ‖1 + ((p : ℕ) : ℂ) ^ (-s)‖ + ‖((p : ℕ) : ℂ) ^ (-s)‖ := norm_sub_le _ _
  rw [norm_one] at htri
  linarith

theorem one_add_primeCpowNeg_ne_zero {s : ℂ} (hs : 1 / 2 ≤ s.re) (p : Nat.Primes) :
    1 + ((p : ℕ) : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have := norm_one_add_primeCpowNeg_ge hs p
  rw [h, norm_zero] at this
  linarith

/-- Uniform coefficient bound on a closed half-plane. -/
theorem norm_coronaPrimeCurrentCoeff_le {s : ℂ} (hs : 1 / 2 ≤ s.re) (p : Nat.Primes) :
    ‖coronaPrimeCurrentCoeff s p‖ ≤
      4 * Real.log ((p : ℕ) : ℝ) * ((p : ℕ) : ℝ) ^ (-s.re) := by
  have hlog : 0 ≤ Real.log ((p : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le)
  have hrpow : (0 : ℝ) < ((p : ℕ) : ℝ) ^ (-s.re) :=
    Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _
  have hden := norm_one_add_primeCpowNeg_ge hs p
  have hdenpos : (0 : ℝ) < ‖1 + ((p : ℕ) : ℂ) ^ (-s)‖ := by linarith
  rw [coronaPrimeCurrentCoeff, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hlog, norm_primeCpowNeg, div_le_iff₀ hdenpos]
  nlinarith [mul_nonneg hlog hrpow.le]

/-! ## Square summability and the Hilbert vector -/

/-- The uniform square majorant of the prime current on `Re s ≥ b`. -/
def coronaPrimeCurrentMajorant (b : ℝ) (p : Nat.Primes) : ℝ :=
  16 * (|Real.log ((p : ℕ) : ℝ)| ^ 2 * ((p : ℕ) : ℝ) ^ (-(2 * b)))

theorem summable_coronaPrimeCurrentMajorant {b : ℝ} (hb : 1 / 2 < b) :
    Summable (coronaPrimeCurrentMajorant b) := by
  have hbeta : (1 : ℝ) < 2 * b := by linarith
  have hnat := summable_abs_log_natCast_pow_mul_rpow_neg 2 (2 * b) hbeta
  have hprime := hnat.comp_injective (i := fun p : Nat.Primes => (p : ℕ)) Subtype.coe_injective
  exact (hprime.mul_left 16).congr fun p => rfl

theorem norm_sq_coronaPrimeCurrentCoeff_le {s : ℂ} {b : ℝ} (hb : 1 / 2 ≤ b) (hsb : b ≤ s.re)
    (p : Nat.Primes) :
    ‖coronaPrimeCurrentCoeff s p‖ ^ 2 ≤ coronaPrimeCurrentMajorant b p := by
  have hs : 1 / 2 ≤ s.re := le_trans hb hsb
  have hle := norm_coronaPrimeCurrentCoeff_le hs p
  have hlog : 0 ≤ Real.log ((p : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le)
  have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.one_lt.le
  have hrpow : (0 : ℝ) < ((p : ℕ) : ℝ) ^ (-s.re) :=
    Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _
  have hexp : ((p : ℕ) : ℝ) ^ (-s.re) ≤ ((p : ℕ) : ℝ) ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have hsq : ‖coronaPrimeCurrentCoeff s p‖ ^ 2 ≤
      (4 * Real.log ((p : ℕ) : ℝ) * ((p : ℕ) : ℝ) ^ (-b)) ^ 2 := by
    have hnonneg : 0 ≤ 4 * Real.log ((p : ℕ) : ℝ) * ((p : ℕ) : ℝ) ^ (-s.re) := by positivity
    have hchain : ‖coronaPrimeCurrentCoeff s p‖ ≤
        4 * Real.log ((p : ℕ) : ℝ) * ((p : ℕ) : ℝ) ^ (-b) := by
      refine le_trans hle ?_
      have := mul_le_mul_of_nonneg_left hexp (by positivity : (0:ℝ) ≤ 4 * Real.log ((p : ℕ) : ℝ))
      linarith [this]
    exact pow_le_pow_left₀ (norm_nonneg _) hchain 2
  refine le_trans hsq (le_of_eq ?_)
  rw [coronaPrimeCurrentMajorant, abs_of_nonneg hlog]
  rw [show (-(2 * b)) = (-b) + (-b) by ring, Real.rpow_add (by exact_mod_cast p.prop.pos)]
  ring

theorem summable_norm_sq_coronaPrimeCurrentCoeff {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun p : Nat.Primes => ‖coronaPrimeCurrentCoeff s p‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun p => by positivity)
    (fun p => norm_sq_coronaPrimeCurrentCoeff_le (le_of_lt hs) le_rfl p)
    (summable_coronaPrimeCurrentMajorant hs)

/-- **The prime current is an `ℓ²` vector on `Re s > 1/2`.** -/
def coronaPrimeCurrentLp {s : ℂ} (hs : 1 / 2 < s.re) : lp (fun _ : Nat.Primes => ℂ) 2 :=
  ⟨coronaPrimeCurrentCoeff s,
    HilbertSchmidt.memℓp_of_sq (summable_norm_sq_coronaPrimeCurrentCoeff hs)⟩

theorem coronaPrimeCurrentLp_apply {s : ℂ} (hs : 1 / 2 < s.re) (p : Nat.Primes) :
    coronaPrimeCurrentLp hs p = coronaPrimeCurrentCoeff s p := rfl

/-- Exact `ℓ²` energy of the prime current. -/
theorem norm_coronaPrimeCurrentLp_sq {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖coronaPrimeCurrentLp hs‖ ^ 2 = ∑' p : Nat.Primes, ‖coronaPrimeCurrentCoeff s p‖ ^ 2 := by
  rw [HilbertSchmidt.lp_norm_sq_eq]
  rfl

/-- The `ℓ²` energy is bounded by the uniform majorant of any admissible half-plane. -/
theorem norm_coronaPrimeCurrentLp_sq_le {s : ℂ} {b : ℝ} (hb : 1 / 2 < b) (hsb : b ≤ s.re)
    (hs : 1 / 2 < s.re) :
    ‖coronaPrimeCurrentLp hs‖ ^ 2 ≤ ∑' p : Nat.Primes, coronaPrimeCurrentMajorant b p := by
  rw [norm_coronaPrimeCurrentLp_sq]
  exact Summable.tsum_le_tsum
    (fun p => norm_sq_coronaPrimeCurrentCoeff_le (le_of_lt hb) hsb p)
    (summable_norm_sq_coronaPrimeCurrentCoeff hs)
    (summable_coronaPrimeCurrentMajorant hb)

/-! ## The Hilbert-valued field and its holomorphy -/

/-- The prime-current field as an `ℓ²`-valued function of `s`, defined by its prime sections. -/
def coronaPrimeCurrentField (s : ℂ) : lp (fun _ : Nat.Primes => ℂ) 2 :=
  ∑' p : Nat.Primes, lp.single 2 p (coronaPrimeCurrentCoeff s p)

theorem coronaPrimeCurrentField_eq {s : ℂ} (hs : 1 / 2 < s.re) :
    coronaPrimeCurrentField s = coronaPrimeCurrentLp hs := by
  rw [coronaPrimeCurrentField]
  exact (lp.hasSum_single (by norm_num) (coronaPrimeCurrentLp hs)).tsum_eq

theorem coronaPrimeCurrentField_apply {s : ℂ} (hs : 1 / 2 < s.re) (p : Nat.Primes) :
    coronaPrimeCurrentField s p = coronaPrimeCurrentCoeff s p := by
  rw [coronaPrimeCurrentField_eq hs]
  rfl

/-- The finite prime section of the current field. -/
def coronaPrimeCurrentSection (T : Finset Nat.Primes) (s : ℂ) : lp (fun _ : Nat.Primes => ℂ) 2 :=
  ∑ p ∈ T, lp.single 2 p (coronaPrimeCurrentCoeff s p)

/-- Coordinates of a finite superposition of prime basis vectors. -/
theorem lp_sum_single_apply (T : Finset Nat.Primes) (c : Nat.Primes → ℂ) (q : Nat.Primes) :
    ((∑ p ∈ T, lp.single 2 p (c p) : lp (fun _ : Nat.Primes => ℂ) 2) : Nat.Primes → ℂ) q =
      if q ∈ T then c q else 0 := by
  classical
  rw [lp.coeFn_sum, Finset.sum_apply]
  rw [show (fun p => (lp.single 2 p (c p) : Nat.Primes → ℂ) q) =
      fun p => if q = p then c p else 0 by
    funext p
    rw [lp.single_apply, Pi.single_apply]]
  simp

theorem coronaPrimeCurrentSection_apply (T : Finset Nat.Primes) (s : ℂ) (q : Nat.Primes) :
    coronaPrimeCurrentSection T s q =
      if q ∈ T then coronaPrimeCurrentCoeff s q else 0 :=
  lp_sum_single_apply T (coronaPrimeCurrentCoeff s) q

/-- The prime tail of the current field, as an explicit `ℓ²` vector. -/
def coronaPrimeCurrentTail {s : ℂ} (hs : 1 / 2 < s.re) (T : Finset Nat.Primes) :
    lp (fun _ : Nat.Primes => ℂ) 2 := by
  classical
  exact ⟨fun p => if p ∈ T then 0 else coronaPrimeCurrentCoeff s p,
    HilbertSchmidt.memℓp_of_sq
      (Summable.of_nonneg_of_le (fun p => by positivity)
        (fun p => by
          by_cases hp : p ∈ T <;> simp [hp])
        (summable_norm_sq_coronaPrimeCurrentCoeff hs))⟩

theorem coronaPrimeCurrentTail_apply {s : ℂ} (hs : 1 / 2 < s.re) (T : Finset Nat.Primes)
    (p : Nat.Primes) :
    coronaPrimeCurrentTail hs T p = if p ∈ T then 0 else coronaPrimeCurrentCoeff s p := by
  classical rfl

theorem coronaPrimeCurrentField_sub_section {s : ℂ} (hs : 1 / 2 < s.re) (T : Finset Nat.Primes) :
    coronaPrimeCurrentField s - coronaPrimeCurrentSection T s = coronaPrimeCurrentTail hs T := by
  classical
  apply Subtype.ext
  funext p
  rw [lp.coeFn_sub]
  simp only [Pi.sub_apply]
  rw [coronaPrimeCurrentField_apply hs, coronaPrimeCurrentSection_apply,
    coronaPrimeCurrentTail_apply hs]
  by_cases hp : p ∈ T <;> simp [hp]

theorem norm_coronaPrimeCurrentTail_sq {s : ℂ} (hs : 1 / 2 < s.re) (T : Finset Nat.Primes) :
    ‖coronaPrimeCurrentTail hs T‖ ^ 2 =
      ∑' p : {x : Nat.Primes // x ∉ T}, ‖coronaPrimeCurrentCoeff s (p : Nat.Primes)‖ ^ 2 := by
  classical
  rw [HilbertSchmidt.lp_norm_sq_eq]
  have hfun : (fun p : Nat.Primes => ‖(coronaPrimeCurrentTail hs T : Nat.Primes → ℂ) p‖ ^ 2) =
      fun p : Nat.Primes => if p ∈ T then 0 else ‖coronaPrimeCurrentCoeff s p‖ ^ 2 := by
    funext p
    rw [coronaPrimeCurrentTail_apply hs]
    by_cases hp : p ∈ T <;> simp [hp]
  rw [hfun]
  have hsupport :
      Function.support (fun p : Nat.Primes =>
        if p ∈ T then 0 else ‖coronaPrimeCurrentCoeff s p‖ ^ 2) ⊆ {x : Nat.Primes | x ∉ T} := by
    intro p hp
    by_contra hmem
    simp only [Set.mem_setOf_eq, not_not] at hmem
    exact hp (by simp [hmem])
  rw [← tsum_subtype_eq_of_support_subset hsupport]
  apply tsum_congr
  intro p
  have hp : (p : Nat.Primes) ∉ T := p.2
  simp [hp]

theorem norm_coronaPrimeCurrentTail_sq_le {s : ℂ} {b : ℝ} (hb : 1 / 2 < b) (hsb : b ≤ s.re)
    (hs : 1 / 2 < s.re) (T : Finset Nat.Primes) :
    ‖coronaPrimeCurrentTail hs T‖ ^ 2 ≤
      ∑' p : {x : Nat.Primes // x ∉ T}, coronaPrimeCurrentMajorant b (p : Nat.Primes) := by
  rw [norm_coronaPrimeCurrentTail_sq]
  exact Summable.tsum_le_tsum
    (fun p => norm_sq_coronaPrimeCurrentCoeff_le (le_of_lt hb) hsb (p : Nat.Primes))
    ((summable_norm_sq_coronaPrimeCurrentCoeff hs).subtype _)
    ((summable_coronaPrimeCurrentMajorant hb).subtype _)

/-- **Locally uniform convergence of the finite prime sections.** -/
theorem tendstoUniformlyOn_coronaPrimeCurrentSection {b : ℝ} (hb : 1 / 2 < b) :
    TendstoUniformlyOn coronaPrimeCurrentSection coronaPrimeCurrentField atTop
      {s : ℂ | b < s.re} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have htail := tendsto_tsum_compl_atTop_zero (coronaPrimeCurrentMajorant b)
  have hev : ∀ᶠ T : Finset Nat.Primes in atTop,
      ∑' p : {x : Nat.Primes // x ∉ T}, coronaPrimeCurrentMajorant b (p : Nat.Primes) <
        ε ^ 2 := by
    have hpos : (0 : ℝ) < ε ^ 2 := by positivity
    exact htail (Iio_mem_nhds hpos)
  filter_upwards [hev] with T hT s hsmem
  have hsre : b < s.re := hsmem
  have hs : 1 / 2 < s.re := lt_trans hb hsre
  have hnormsq : ‖coronaPrimeCurrentField s - coronaPrimeCurrentSection T s‖ ^ 2 < ε ^ 2 := by
    rw [coronaPrimeCurrentField_sub_section hs T]
    exact lt_of_le_of_lt
      (norm_coronaPrimeCurrentTail_sq_le hb (le_of_lt hsre) hs T) hT
  have hnorm : ‖coronaPrimeCurrentField s - coronaPrimeCurrentSection T s‖ < ε := by
    nlinarith [norm_nonneg (coronaPrimeCurrentField s - coronaPrimeCurrentSection T s)]
  rwa [dist_eq_norm]

/-! ## Holomorphy -/

theorem differentiable_primeCpowNeg (p : Nat.Primes) :
    Differentiable ℂ fun s : ℂ => ((p : ℕ) : ℂ) ^ (-s) := by
  have hne : (((p : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr p.prop.ne_zero
  exact (differentiable_neg).const_cpow (Or.inl hne)

theorem differentiableOn_coronaPrimeCurrentCoeff (p : Nat.Primes) {b : ℝ} (hb : 1 / 2 ≤ b) :
    DifferentiableOn ℂ (fun s : ℂ => coronaPrimeCurrentCoeff s p) {s : ℂ | b < s.re} := by
  apply DifferentiableOn.div
  · exact ((differentiable_primeCpowNeg p).const_mul _).differentiableOn
  · exact ((differentiable_primeCpowNeg p).const_add _).differentiableOn
  · intro s hs
    have hsre : b < s.re := hs
    exact one_add_primeCpowNeg_ne_zero (by linarith) p

theorem lp_single_eq_smul (p : Nat.Primes) (c : ℂ) :
    (lp.single 2 p c : lp (fun _ : Nat.Primes => ℂ) 2) =
      c • (lp.single 2 p (1 : ℂ) : lp (fun _ : Nat.Primes => ℂ) 2) := by
  classical
  rw [← lp.single_smul]
  simp

theorem differentiableOn_coronaPrimeCurrentSection (T : Finset Nat.Primes) {b : ℝ}
    (hb : 1 / 2 ≤ b) :
    DifferentiableOn ℂ (coronaPrimeCurrentSection T) {s : ℂ | b < s.re} := by
  classical
  have hfun : coronaPrimeCurrentSection T =
      fun s : ℂ => ∑ p ∈ T, coronaPrimeCurrentCoeff s p •
        (lp.single 2 p (1 : ℂ) : lp (fun _ : Nat.Primes => ℂ) 2) := by
    funext s
    rw [coronaPrimeCurrentSection]
    exact Finset.sum_congr rfl fun p _ => lp_single_eq_smul p _
  rw [hfun]
  apply DifferentiableOn.fun_sum
  intro p _
  exact (differentiableOn_coronaPrimeCurrentCoeff p hb).smul_const _

/-- **The prime current is a holomorphic `ℓ²`-valued field on `Re s > 1/2`.**  It is the locally
uniform limit of its finite prime sections, each of which is entire in the half-plane. -/
theorem differentiableOn_coronaPrimeCurrentField :
    DifferentiableOn ℂ coronaPrimeCurrentField {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  have hsre : 1 / 2 < s.re := hs
  set b : ℝ := (1 / 2 + s.re) / 2 with hbdef
  have hb : 1 / 2 < b := by rw [hbdef]; linarith
  have hbs : b < s.re := by rw [hbdef]; linarith
  have hopen : IsOpen {z : ℂ | b < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ coronaPrimeCurrentField {z : ℂ | b < z.re} := by
    refine (tendstoUniformlyOn_coronaPrimeCurrentSection hb).tendstoLocallyUniformlyOn.differentiableOn
      ?_ hopen
    filter_upwards with T
    exact differentiableOn_coronaPrimeCurrentSection T (le_of_lt hb)
  have hmem : {z : ℂ | b < z.re} ∈ nhds s := hopen.mem_nhds hbs
  exact ((hdiff.differentiableAt hmem).differentiableWithinAt)

/-- No prime coordinate of the current field has a pole on `Re s > 1/2`. -/
theorem differentiableOn_coronaPrimeCurrentCoeff_halfPlane (p : Nat.Primes) :
    DifferentiableOn ℂ (fun s : ℂ => coronaPrimeCurrentCoeff s p) {s : ℂ | 1 / 2 < s.re} :=
  differentiableOn_coronaPrimeCurrentCoeff p le_rfl

end RHTower
