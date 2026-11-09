import GaloisForLFunctions.ExceptionalLayerTheory.TheDirichletPoleControlsTheInfiniteDivisor
import GaloisForLFunctions.ExceptionalLayerTheory.InfinitePowerSumsDetectAMaximalTerm
import GaloisForLFunctions.RHTower.DeBruijnTopZeroVelocity

/-!
# Deuring–Heilbronn repulsion for the complete Dirichlet divisor

A real zero of a primitive nonprincipal quadratic Dirichlet L-function
repels the other zeros of its product with ζ. The constant is absolute,
and the logarithmic conductor scale is `log(q (|Im ρ| + 3))`.

The proof detects a term in the complete reciprocal-square family using
an infinite power sum, then compares that moment with the Euler-positive
pole cancellation bound. Exactly one exceptional multiplicity copy is
removed; all other copies and the infinite remainder are retained.
-/

open Complex Set
open GaloisForLFunctions.EntireZeroDivisor

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem repulsion_mass_normalization {δ L S R : ℝ}
    (hδ : 0 ≤ δ) (hL : 1 ≤ L) (hR : 0 < R)
    (hS : S ≤ 32 * (1 / (δ + 1 / (2 * L)) ^ 2 + L / (δ + 1 / (2 * L))))
    (hTarget : 1 / (δ + 1 / (2 * L) + δ) ^ 2 ≤ R) :
    S / R ≤ 192 * (1 + δ * L) ∧ (δ + 1 / (2 * L))⁻¹ ^ 2 ≤ 4 * R := by
  let a := δ + 1 / (2 * L)
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have ha : 0 < a := add_pos_of_nonneg_of_pos hδ (by positivity)
  have hδa : δ ≤ a := le_add_of_nonneg_right (by positivity)
  have hsum : 0 < a + δ := add_pos_of_pos_of_nonneg ha hδ
  have hsquare : (a + δ) ^ 2 ≤ 4 * a ^ 2 := by
    have hh := pow_le_pow_left₀ hsum.le (show a + δ ≤ 2 * a by linarith only [hδa]) 2
    nlinarith only [hh]
  have hR' : 1 / (4 * a ^ 2) ≤ R :=
    (one_div_le_one_div_of_le (by positivity) hsquare).trans hTarget
  have hcross : 1 ≤ R * (4 * a ^ 2) := (div_le_iff₀ (by positivity)).mp hR'
  have hInv : R⁻¹ ≤ 4 * a ^ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hR).mpr
    nlinarith only [hcross]
  have hRadius : a⁻¹ ^ 2 ≤ 4 * R := by
    rw [inv_pow, inv_eq_one_div]
    apply (div_le_iff₀ (sq_pos_of_pos ha)).mpr
    nlinarith only [hcross]
  refine ⟨?_, hRadius⟩
  have hscale : (32 * (1 / a ^ 2 + L / a)) * (4 * a ^ 2) = 128 * (1 + a * L) := by
    field_simp
    ring
  have haL : a * L = δ * L + 1 / 2 := by
    dsimp only [a]
    field_simp
  calc
    S / R = S * R⁻¹ := div_eq_mul_inv _ _
    _ ≤ (32 * (1 / a ^ 2 + L / a)) * (4 * a ^ 2) :=
      mul_le_mul hS hInv (inv_nonneg.mpr hR.le) (by positivity)
    _ = 128 * (1 + a * L) := hscale
    _ ≤ 192 * (1 + δ * L) := by
      rw [haL]
      nlinarith only [mul_nonneg hδ hLp.le]

private def exceptionalRepulsionConstant : ℝ := 64 * Real.exp 61440 + 61441

private theorem exceptionalRepulsionConstant_pos : 0 < exceptionalRepulsionConstant := by
  unfold exceptionalRepulsionConstant
  positivity

/-- The detected moment and pole cancellation force an exponential
lower bound for the exceptional zero's distance from one. -/
private theorem detected_moment_forces_repulsion {α δ L η R : ℝ} {k : ℕ}
    (hα : 0 < α) (hδ : 0 ≤ δ) (hL : 0 < L) (hη : 0 ≤ η) (hR : 0 < R)
    (hInv : α⁻¹ ≤ 2 * L) (hRadius : α⁻¹ ^ 2 ≤ 4 * R)
    (hK : (k : ℝ) ≤ 12288 * (1 + δ * L))
    (hMoment : R ^ k / 8 < 4 * (k : ℝ) * η * α⁻¹ ^ (2 * k + 1)) :
    1 ≤ exceptionalRepulsionConstant * η * L *
      Real.exp (exceptionalRepulsionConstant * δ * L) := by
  have hB : 0 ≤ 4 * (k : ℝ) * η * α⁻¹ := by positivity
  have hPower := pow_le_pow_left₀ (sq_nonneg α⁻¹) hRadius k
  have hUpper : R ^ k / 8 < (4 * (k : ℝ) * η * α⁻¹) * 4 ^ k * R ^ k := by
    calc
      R ^ k / 8 < 4 * (k : ℝ) * η * α⁻¹ ^ (2 * k + 1) := hMoment
      _ = (4 * (k : ℝ) * η * α⁻¹) * (α⁻¹ ^ 2) ^ k := by rw [← pow_mul, pow_succ]; ring
      _ ≤ (4 * (k : ℝ) * η * α⁻¹) * (4 * R) ^ k := mul_le_mul_of_nonneg_left hPower hB
      _ = _ := by rw [mul_pow]; ring
  have hFactor : 1 / 8 < (4 * (k : ℝ) * η * α⁻¹) * 4 ^ k := by
    by_contra hn
    have hh := mul_le_mul_of_nonneg_right (not_lt.mp hn) (pow_nonneg hR.le k)
    linarith only [hUpper, hh]
  have hScale := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hInv (by positivity : 0 ≤ 4 * (k : ℝ) * η))
    (by positivity : 0 ≤ (4 : ℝ) ^ k)
  have hDetect : 1 < 64 * (k : ℝ) * η * L * 4 ^ k := by
    nlinarith only [hFactor, hScale]
  have hkExp : (k : ℝ) ≤ Real.exp k := by
    linarith only [Real.add_one_le_exp (k : ℝ)]
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith only [Real.add_one_le_exp (4 : ℝ)]
  have hfourPow : (4 : ℝ) ^ k ≤ Real.exp ((k : ℝ) * 4) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) hfour k
  have hkPower : (k : ℝ) * 4 ^ k ≤ Real.exp (5 * (k : ℝ)) := by
    calc
      _ ≤ Real.exp k * Real.exp ((k : ℝ) * 4) :=
        mul_le_mul hkExp hfourPow (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hkArg : 5 * (k : ℝ) ≤ 61440 + 61440 * δ * L := by nlinarith only [hK]
  have hkEnvelope : Real.exp (5 * (k : ℝ)) ≤ Real.exp 61440 * Real.exp (61440 * δ * L) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hkArg
  have hC₀ : 64 * Real.exp 61440 ≤ exceptionalRepulsionConstant := by
    unfold exceptionalRepulsionConstant
    linarith
  have hC₁ : 61440 ≤ exceptionalRepulsionConstant := by
    unfold exceptionalRepulsionConstant
    linarith only [Real.exp_pos (61440 : ℝ)]
  have hExpArg : 61440 * δ * L ≤ exceptionalRepulsionConstant * δ * L := by
    have hh := mul_le_mul_of_nonneg_right hC₁ (mul_nonneg hδ hL.le)
    simpa only [mul_assoc] using hh
  have hFinal : 64 * (k : ℝ) * η * L * 4 ^ k ≤
      exceptionalRepulsionConstant * η * L * Real.exp (exceptionalRepulsionConstant * δ * L) := by
    calc
      _ = (64 * η * L) * ((k : ℝ) * 4 ^ k) := by ring
      _ ≤ (64 * η * L) * Real.exp (5 * (k : ℝ)) :=
        mul_le_mul_of_nonneg_left hkPower (by positivity)
      _ ≤ (64 * η * L) * (Real.exp 61440 * Real.exp (61440 * δ * L)) :=
        mul_le_mul_of_nonneg_left hkEnvelope (by positivity)
      _ = (64 * Real.exp 61440) * (η * L) * Real.exp (61440 * δ * L) := by ring
      _ ≤ exceptionalRepulsionConstant * (η * L) * Real.exp (exceptionalRepulsionConstant * δ * L) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hC₀ (mul_nonneg hη hL.le))
          (Real.exp_le_exp.mpr hExpArg) (Real.exp_pos _).le
          (mul_nonneg exceptionalRepulsionConstant_pos.le (mul_nonneg hη hL.le))
      _ = _ := by ring
  exact (hDetect.trans_le hFinal).le


/-- Logarithmic conductor scale, with an absolute positive lower bound. -/
def exceptionalHeightLog (q : ℕ) (t : ℝ) : ℝ :=
  1 + Real.log q + Real.log (|t| + 3)

private theorem exceptional_copy_repulsion {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (hreal : χ.IsQuadratic)
    (i₁ j : ExceptionalZeroCopy χ) {β : ℝ} (hβ : exceptionalZero χ i₁ = (β : ℂ))
    (hj : j ≠ i₁) (hhalf : 1 / 2 ≤ (exceptionalZero χ j).re) :
    Real.log (1 / (exceptionalRepulsionConstant * (1 - β) *
      exceptionalHeightLog q (exceptionalZero χ j).im)) /
        (exceptionalRepulsionConstant * exceptionalHeightLog q (exceptionalZero χ j).im) ≤
      1 - (exceptionalZero χ j).re := by
  let ρ := exceptionalZero χ j
  let δ := 1 - ρ.re
  let L := exceptionalHeightLog q ρ.im
  let α := δ + 1 / (2 * L)
  let σ := 1 + α
  let z := pairedExceptionalResolvent χ i₁ σ ρ.im
  have hδ : 0 < δ := by
    have hh := (exceptionalZero_strip hχ hprim j).2
    dsimp only [δ, ρ]
    linarith only [hh]
  have hδhalf : δ ≤ 1 / 2 := by dsimp only [δ, ρ]; linarith only [hhalf]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hL1 : 1 ≤ L := by
    have hqlog := Real.log_nonneg hq1
    have htlog := Real.log_nonneg (show 1 ≤ |ρ.im| + 3 by linarith only [abs_nonneg ρ.im])
    dsimp only [L, exceptionalHeightLog]
    linarith only [hqlog, htlog]
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL1
  have hα : 0 < α := by dsimp only [α]; positivity
  have hσ : 1 < σ := by dsimp only [σ]; linarith only [hα]
  have hσα : σ - 1 = α := by dsimp only [σ]; ring
  have hsmall : 1 / (2 * L) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith only [hL1])
  have hσ2 : σ ≤ 2 := by dsimp only [σ, α]; linarith only [hsmall, hδhalf]
  have hInv : α⁻¹ ≤ 2 * L := by
    have hlow : 1 / (2 * L) ≤ α := by dsimp only [α]; linarith only [hδ]
    have hc := (div_le_iff₀ (by positivity : 0 < 2 * L)).mp hlow
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hα).mpr
    nlinarith only [hc]
  have hgap : σ - ρ.re = α + δ := by dsimp only [σ, δ]; ring
  have hTargetNorm : ‖z (.inr j)‖ = 1 / (α + δ) ^ 2 := by
    dsimp only [z, ρ]
    rw [pairedExceptionalResolvent_target i₁ j hj σ, Complex.norm_real,
      Real.norm_of_nonneg (sq_nonneg _)]
    change (σ - ρ.re)⁻¹ ^ 2 = _
    rw [hgap, inv_pow, inv_eq_one_div]
  have hTargetNe : z (.inr j) ≠ 0 := by
    apply norm_pos_iff.mp
    rw [hTargetNorm]
    positivity
  have hsum : Summable (fun i => ‖z i‖) := pairedExceptionalResolvent_norm_summable hχ hprim i₁ hσ ρ.im
  obtain ⟨u, k, hR, hmax, hk, hkMass, hDetect⟩ :=
    infinite_real_power_sum_detects_maximal_term hsum (.inr j) hTargetNe
  let R := ‖z u‖
  have hTarget : 1 / (α + δ) ^ 2 ≤ R := by
    have hh := hmax (.inr j)
    rwa [hTargetNorm] at hh
  have hMass := pairedExceptionalResolvent_mass_le hχ hprim hreal i₁ hσ hσ2 ρ.im
  change (∑' i, ‖z i‖) ≤ 32 * (1 / (σ - 1) ^ 2 + L / (σ - 1)) at hMass
  rw [hσα] at hMass
  have hNormalized := repulsion_mass_normalization hδ.le hL1 hR hMass hTarget
  have hkBound : (k : ℝ) ≤ 12288 * (1 + δ * L) := by
    have hh := mul_le_mul_of_nonneg_left hNormalized.1 (by norm_num : (0 : ℝ) ≤ 64)
    simp only [mul_div_assoc] at hkMass
    linarith only [hkMass, hh]
  have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hMoment := pairedExceptionalResolvent_moment_le hχ hprim hreal i₁ hβ hσ ρ.im hkpos
  change (∑' i, z i ^ k).re ≤ 4 * (k : ℝ) * (1 - β) * (σ - 1)⁻¹ ^ (2 * k + 1) at hMoment
  rw [hσα] at hMoment
  have hη : 0 < 1 - β := by
    have hh := (exceptionalZero_strip hχ hprim i₁).2
    rw [hβ, ofReal_re] at hh
    linarith only [hh]
  have hLaw := detected_moment_forces_repulsion hα hδ.le hLp hη.le hR hInv
    hNormalized.2 hkBound (hDetect.trans_le hMoment)
  have hProduct : 0 < exceptionalRepulsionConstant * (1 - β) * L :=
    mul_pos (mul_pos exceptionalRepulsionConstant_pos hη) hLp
  have hFraction : 1 / (exceptionalRepulsionConstant * (1 - β) * L) ≤
      Real.exp (exceptionalRepulsionConstant * δ * L) := by
    apply (div_le_iff₀ hProduct).mpr
    nlinarith only [hLaw]
  have hLog := Real.log_le_log (one_div_pos.mpr hProduct) hFraction
  rw [Real.log_exp] at hLog
  change Real.log (1 / (exceptionalRepulsionConstant * (1 - β) * L)) /
    (exceptionalRepulsionConstant * L) ≤ δ
  apply (div_le_iff₀ (mul_pos exceptionalRepulsionConstant_pos hLp)).mpr
  nlinarith only [hLog]

/-- Deuring–Heilbronn repulsion for the actual infinite divisor of
`ζ(s)L(s,χ)`, with a constant independent of conductor, height, and zeros.
Exactly one exceptional multiplicity copy is exempted. -/
theorem exists_dirichlet_exceptional_zero_repulsion :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → χ.IsPrimitive → χ.IsQuadratic →
      ∀ (i₁ j : ExceptionalZeroCopy χ) (β : ℝ),
        exceptionalZero χ i₁ = (β : ℂ) → j ≠ i₁ →
        1 / 2 ≤ (exceptionalZero χ j).re →
        Real.log (1 / (C * (1 - β) * exceptionalHeightLog q (exceptionalZero χ j).im)) /
          (C * exceptionalHeightLog q (exceptionalZero χ j).im) ≤ 1 - (exceptionalZero χ j).re := by
  refine ⟨exceptionalRepulsionConstant, exceptionalRepulsionConstant_pos, ?_⟩
  intro q inst χ hχ hprim hreal i₁ j β hβ hj hhalf
  exact exceptional_copy_repulsion hχ hprim hreal i₁ j hβ hj hhalf


variable {q : ℕ} [NeZero q]

private theorem exceptionalCompletion_zero_of_L_zero {χ : DirichletCharacter ℂ q}
    {s : ℂ} (hs : 0 < s.re) (hL : χ.LFunction s = 0) : exceptionalCompletion χ s = 0 := by
  have hs0 : s ≠ 0 := by intro h; rw [h, zero_re] at hs; exact (lt_irrefl _ hs)
  obtain ⟨d, hd, hgamma⟩ := RHTower.gammaFactor_eq_Gammaℝ χ
  have hd0 : 0 ≤ d := by rcases hd with rfl | rfl <;> norm_num
  have hGamma : χ.gammaFactor s ≠ 0 := by
    rw [hgamma s]
    exact Gammaℝ_ne_zero_of_re_pos (by rw [add_re, ofReal_re]; linarith only [hs, hd0])
  have hDiv := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)
  have hComp := (div_eq_iff hGamma).mp hDiv.symm
  rw [hL, zero_mul] at hComp
  rw [exceptionalCompletion, hComp, mul_zero]

private theorem exceptionalCompletion_zero_of_product_zero {χ : DirichletCharacter ℂ q}
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hzero : riemannZeta s = 0 ∨ χ.LFunction s = 0) : exceptionalCompletion χ s = 0 := by
  rcases hzero with hζ | hL
  · have hxi := (RHTower.xi_eq_zero_iff hs hs1).mpr hζ
    rw [exceptionalCompletion, hxi, zero_mul, zero_mul]
  · exact exceptionalCompletion_zero_of_L_zero hs hL

private theorem exists_exceptionalZero_copy {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {ρ : ℂ} (hρ : exceptionalCompletion χ ρ = 0) :
    ∃ i : ExceptionalZeroCopy χ, exceptionalZero χ i = ρ := by
  let f : ℂ → ℂ := fun z => exceptionalCompletion χ (z + 2)
  have hf : AnalyticOnNhd ℂ f univ :=
    ((exceptionalCompletion_entire hχ).comp (differentiable_id.add_const 2)).differentiableOn.analyticOnNhd isOpen_univ
  have hf0 : f 0 ≠ 0 := by simpa only [f, zero_add] using exceptionalCompletion_two_ne_zero hχ hprim
  have hfρ : f (ρ - 2) = 0 := by simpa only [f, sub_add_cancel] using hρ
  obtain ⟨i, hi⟩ := RHTower.DeBruijn.exists_zeroCopy_of_eq_zero hf hf0 hfρ
  refine ⟨i, ?_⟩
  change zeroCopyPoint f i + 2 = ρ
  rw [hi, sub_add_cancel]

/-- Classical Deuring–Heilbronn repulsion in the usual logarithmic
conductor scale, for actual zeros of `ζ` or `L(χ)`. The constant is
uniform in the primitive real character, the height, and both zeros. -/
theorem exists_deuring_heilbronn_repulsion :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → χ.IsPrimitive → χ.IsQuadratic →
      ∀ (β : ℝ) (ρ : ℂ), 0 < β → χ.LFunction (β : ℂ) = 0 →
        1 / 2 ≤ ρ.re → ρ ≠ 1 → (riemannZeta ρ = 0 ∨ χ.LFunction ρ = 0) →
        ρ ≠ (β : ℂ) →
        Real.log (1 / (C * (1 - β) * Real.log ((q : ℝ) * (|ρ.im| + 3)))) /
          (C * Real.log ((q : ℝ) * (|ρ.im| + 3))) ≤ 1 - ρ.re := by
  obtain ⟨C, hC, hBound⟩ := exists_dirichlet_exceptional_zero_repulsion
  let A : ℝ := 1 + (Real.log 3)⁻¹
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨C * A, mul_pos hC hA, ?_⟩
  intro q inst χ hχ hprim hreal β ρ hβ hL hhalf hρ1 hzero hneq
  have hEβ := exceptionalCompletion_zero_of_L_zero (show 0 < (β : ℂ).re from hβ) hL
  have hρpos : 0 < ρ.re := by linarith only [hhalf]
  have hEρ := exceptionalCompletion_zero_of_product_zero hρpos hρ1 hzero
  obtain ⟨i₁, hi₁⟩ := exists_exceptionalZero_copy hχ hprim hEβ
  obtain ⟨j, hj⟩ := exists_exceptionalZero_copy hχ hprim hEρ
  have hji : j ≠ i₁ := by
    intro heq
    apply hneq
    rw [← hj, heq, hi₁]
  have hIndex := hBound χ hχ hprim hreal i₁ j β hi₁ hji (by simpa only [hj] using hhalf)
  rw [hj] at hIndex
  let Q : ℝ := Real.log ((q : ℝ) * (|ρ.im| + 3))
  let L : ℝ := exceptionalHeightLog q ρ.im
  have hqpos : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hQeq : Q = Real.log q + Real.log (|ρ.im| + 3) := by
    dsimp only [Q]
    rw [Real.log_mul hqpos.ne' (by positivity : |ρ.im| + 3 ≠ 0)]
  have hQge : Real.log 3 ≤ Q := by
    have ht := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
      (show 3 ≤ |ρ.im| + 3 by linarith only [abs_nonneg ρ.im])
    have hq := Real.log_nonneg hq1
    rw [hQeq]
    linarith only [ht, hq]
  have hQ : 0 < Q := hlog3.trans_le hQge
  have hLeq : L = 1 + Q := by dsimp only [L, exceptionalHeightLog]; rw [hQeq]; ring
  have hLp : 0 < L := by rw [hLeq]; linarith only [hQ]
  have hScale : L ≤ A * Q := by
    have hh : 1 ≤ Q / Real.log 3 := (le_div_iff₀ hlog3).mpr (by simpa using hQge)
    rw [div_eq_mul_inv] at hh
    rw [hLeq]
    dsimp only [A]
    nlinarith only [hh]
  have hη : 0 < 1 - β := by
    have hh := (exceptionalCompletion_zero_strip hχ hprim hEβ).2
    rw [ofReal_re] at hh
    linarith only [hh]
  have hδ : 0 < 1 - ρ.re := sub_pos.mpr (exceptionalCompletion_zero_strip hχ hprim hEρ).2
  have hP : 0 < C * (1 - β) * L := mul_pos (mul_pos hC hη) hLp
  have hP' : 0 < (C * A) * (1 - β) * Q := mul_pos (mul_pos (mul_pos hC hA) hη) hQ
  have hProd : C * (1 - β) * L ≤ (C * A) * (1 - β) * Q := by
    have hh := mul_le_mul_of_nonneg_left hScale (mul_nonneg hC.le hη.le)
    nlinarith only [hh]
  have hRecip := one_div_le_one_div_of_le hP hProd
  have hLog := Real.log_le_log (one_div_pos.mpr hP') hRecip
  have hOld : Real.log (1 / (C * (1 - β) * L)) ≤ (1 - ρ.re) * (C * L) :=
    (div_le_iff₀ (mul_pos hC hLp)).mp hIndex
  have hExp := mul_le_mul_of_nonneg_left hScale (mul_nonneg hC.le hδ.le)
  change Real.log (1 / ((C * A) * (1 - β) * Q)) / ((C * A) * Q) ≤ 1 - ρ.re
  apply (div_le_iff₀ (mul_pos (mul_pos hC hA) hQ)).mpr
  nlinarith only [hLog, hOld, hExp]

end GaloisForLFunctions.ExceptionalLayerTheory

#print axioms GaloisForLFunctions.ExceptionalLayerTheory.exists_dirichlet_exceptional_zero_repulsion
#print axioms GaloisForLFunctions.ExceptionalLayerTheory.exists_deuring_heilbronn_repulsion
