import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerPoissonCalderonGraph
import GaloisForLFunctions.RHTower.BoundedExponentPoissonNonlanding

/-!
# Value-level landing of Meyer's Poisson operator in a rapid two-ended target

For every source vector in Meyer's even, two-endpoint Schwartz space, the positive
dilation sum

`Zf(x) = ∑_{n ≥ 1} f(nx)`

is continuous on the positive ray and decays faster than every real power at both
multiplicative ends.  The proof is unconditional:

* local uniform convergence gives continuity;
* the physical zero mode and an arbitrary Schwartz seminorm give large-end decay;
* the Fourier zero mode and signed Poisson summation give small-end decay.

The file then models the positive ray by zero extension to the nonpositive axis.
This support condition is essential: `RapidDecayRay` alone deliberately says
nothing away from the positive ray and would otherwise admit an artificial
negative-support sector.  This remains only a value-level necessary target:
it does not encode smoothness or decay of all multiplicative derivatives and
therefore is not Meyer's full Bruhat--Schwartz `H⁻`.  The full all-weight target
is constructed in `DeningerMeyerStrongLogTarget`.

No Riemann-hypothesis premise, positivity assumption, spectral realization, numerical
computation, or imported source-provenance hypothesis occurs.
-/

open Complex Filter Topology MeasureTheory Set
open scoped SchwartzMap FourierTransform
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Local uniform convergence -/

/-- Meyer's positive dilation sum is continuous on the positive ray. -/
theorem continuousOn_deningerMeyerSum (f : SchwartzMap ℝ ℂ) :
    ContinuousOn (deningerMeyerSum f) (Ioi 0) := by
  intro x hx
  let a : ℝ := x / 2
  let S : ℝ := SchwartzMap.seminorm ℂ 2 0 f
  let u : ℕ → ℝ := fun n =>
    S / (a ^ 2 * (((n : ℝ) + 1) ^ 2))
  have hxpos : 0 < x := hx
  have ha : 0 < a := by
    dsimp [a]
    linarith
  have hsumBase :
      Summable (fun n : ℕ => 1 / ((((n : ℝ) + 1)) ^ 2)) := by
    have h := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
    simpa [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr h
  have hu : Summable u := by
    have hm := hsumBase.mul_left (S / a ^ 2)
    refine hm.congr fun n => ?_
    dsimp [u]
    field_simp
  have hcont : ContinuousOn (deningerMeyerSum f) (Ici a) := by
    change ContinuousOn
      (fun y : ℝ => ∑' n : ℕ, f (((n : ℝ) + 1) * y)) (Ici a)
    refine continuousOn_tsum (fun n => ?_) hu (fun n y hy => ?_)
    · fun_prop
    · have hn : 0 < (n : ℝ) + 1 := by positivity
      have hypos : 0 < y := lt_of_lt_of_le ha hy
      have harg : 0 < ((n : ℝ) + 1) * y := mul_pos hn hypos
      have hsem :=
        SchwartzMap.norm_pow_mul_le_seminorm ℂ f 2
          (((n : ℝ) + 1) * y)
      have hden : 0 < ‖((n : ℝ) + 1) * y‖ ^ 2 :=
        pow_pos (norm_pos_iff.mpr harg.ne') _
      have hraw :
          ‖f (((n : ℝ) + 1) * y)‖ ≤
            S / ‖((n : ℝ) + 1) * y‖ ^ 2 := by
        apply (le_div_iff₀ hden).2
        simpa [S, mul_comm] using hsem
      have hmono :
          S / ‖((n : ℝ) + 1) * y‖ ^ 2 ≤
            S / (a ^ 2 * (((n : ℝ) + 1) ^ 2)) := by
        have hS : 0 ≤ S := by
          dsimp [S]
          positivity
        have hya : a ≤ y := hy
        have hdenle :
            a ^ 2 * (((n : ℝ) + 1) ^ 2) ≤
              ‖((n : ℝ) + 1) * y‖ ^ 2 := by
          rw [Real.norm_eq_abs, abs_of_pos harg, mul_pow]
          have hsquare : a ^ 2 ≤ y ^ 2 := by nlinarith
          simpa [mul_comm] using
            (mul_le_mul_of_nonneg_left hsquare
              (sq_nonneg ((n : ℝ) + 1)))
        have hminor :
            0 < a ^ 2 * (((n : ℝ) + 1) ^ 2) :=
          mul_pos (sq_pos_of_pos ha) (sq_pos_of_pos hn)
        exact div_le_div_of_nonneg_left hS hminor hdenle
      exact hraw.trans hmono
  have hax : a < x := by
    dsimp [a]
    linarith
  exact (hcont x hax.le).continuousAt
    (Ici_mem_nhds hax) |>.continuousWithinAt

/-! ## Quantitative two-ended bounds -/

/--
Arbitrary-power large-end estimate for the positive sum.  The full lattice trace is
twice this sum, so the existing signed Schwartz estimate immediately controls it.
-/
theorem deningerMeyerSum_large_bound
    (f : SchwartzMap ℝ ℂ) (hf : f ∈ DeningerMeyerCap)
    (N : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖deningerMeyerSum f x‖ ≤
      ccmRationalArchimedeanDecayConstant f N /
        x ^ ccmRationalArchimedeanDecayExponent N := by
  obtain ⟨heven, hf0, _⟩ := (deningerMeyerCap_mem_iff f).mp hf
  have htrace :=
    deningerMeyerLatticeTrace_eq_two_sum f heven hf0 hx.ne'
  calc
    ‖deningerMeyerSum f x‖ ≤
        ‖ccmRationalArchimedeanLatticeTrace f x‖ := by
      rw [htrace, norm_mul]
      norm_num
      nlinarith [norm_nonneg (deningerMeyerSum f x)]
    _ ≤ ccmRationalArchimedeanDecayConstant f N /
          x ^ ccmRationalArchimedeanDecayExponent N :=
      ccmRationalArchimedeanLatticeTrace_large_bound f hf0 N hx

/--
Arbitrary-power small-end estimate.  This is the genuinely signed step: the Fourier
zero mode kills the dual zero term before the large-end estimate is reflected.
-/
theorem deningerMeyerSum_small_bound
    (f : SchwartzMap ℝ ℂ) (hf : f ∈ DeningerMeyerCap)
    (N : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖deningerMeyerSum f x‖ ≤
      ccmRationalArchimedeanDecayConstant
          (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ) f) N *
        x ^ (ccmRationalArchimedeanDecayExponent N - 1) := by
  obtain ⟨heven, hf0, hF0⟩ := (deningerMeyerCap_mem_iff f).mp hf
  have htrace :=
    deningerMeyerLatticeTrace_eq_two_sum f heven hf0 hx.ne'
  calc
    ‖deningerMeyerSum f x‖ ≤
        ‖ccmRationalArchimedeanLatticeTrace f x‖ := by
      rw [htrace, norm_mul]
      norm_num
      nlinarith [norm_nonneg (deningerMeyerSum f x)]
    _ ≤ ccmRationalArchimedeanDecayConstant
          (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ) f) N *
          x ^ (ccmRationalArchimedeanDecayExponent N - 1) :=
      ccmRationalArchimedeanLatticeTrace_small_bound f hF0 N hx

/-- The positive sum is `O(x⁻ᵃ)` at infinity for every real exponent `a`. -/
theorem deningerMeyerSum_isBigO_atTop
    (f : SchwartzMap ℝ ℂ) (hf : f ∈ DeningerMeyerCap)
    (a : ℝ) :
    deningerMeyerSum f =O[atTop] fun x : ℝ => x ^ (-a) := by
  let N : ℕ := ⌈max a 0⌉₊
  let p : ℕ := ccmRationalArchimedeanDecayExponent N
  let C : ℝ := ccmRationalArchimedeanDecayConstant f N
  have hCa : 0 ≤ C :=
    ccmRationalArchimedeanDecayConstant_nonneg f N
  have hap : a ≤ (p : ℝ) := by
    have hceil : max a 0 ≤ (N : ℝ) := Nat.le_ceil _
    have hNp : (N : ℝ) ≤ (p : ℝ) := by
      have hnat :
          N ≤ ccmRationalArchimedeanDecayExponent N := by
        simp [ccmRationalArchimedeanDecayExponent]
        omega
      exact_mod_cast hnat
    exact (le_max_left a 0).trans (hceil.trans hNp)
  refine (Asymptotics.IsBigOWith.of_bound (c := C) ?_).isBigO
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hxpos : 0 < x := one_pos.trans_le hx
  have hlarge := deningerMeyerSum_large_bound f hf N hxpos
  have hlarge' :
      ‖deningerMeyerSum f x‖ ≤ C / x ^ p := by
    simpa [C, p] using hlarge
  have hrpow :
      x ^ (-(p : ℝ)) ≤ x ^ (-a) :=
    Real.rpow_le_rpow_of_exponent_le hx (neg_le_neg hap)
  have hrewrite :
      C / x ^ p = C * x ^ (-(p : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_natCast,
      ← Real.rpow_neg hxpos.le]
  rw [show ‖x ^ (-a)‖ = x ^ (-a) by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hxpos.le _)]]
  exact hlarge'.trans_eq hrewrite |>.trans
    (mul_le_mul_of_nonneg_left hrpow hCa)

/-- The positive sum is `O(x⁻ᵇ)` at zero from the right for every real exponent `b`. -/
theorem deningerMeyerSum_isBigO_zero
    (f : SchwartzMap ℝ ℂ) (hf : f ∈ DeningerMeyerCap)
    (b : ℝ) :
    deningerMeyerSum f =O[𝓝[>] 0] fun x : ℝ => x ^ (-b) := by
  let N : ℕ := ⌈max (-b) 0⌉₊
  let q : ℕ := ccmRationalArchimedeanDecayExponent N - 1
  let C : ℝ :=
    ccmRationalArchimedeanDecayConstant
      (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ) f) N
  have hC : 0 ≤ C :=
    ccmRationalArchimedeanDecayConstant_nonneg
      (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ) f) N
  have hbq : -b ≤ (q : ℝ) := by
    have hceil : max (-b) 0 ≤ (N : ℝ) := Nat.le_ceil _
    have hNq : (N : ℝ) ≤ (q : ℝ) := by
      have hnat :
          N ≤ ccmRationalArchimedeanDecayExponent N - 1 := by
        simp [ccmRationalArchimedeanDecayExponent]
        omega
      exact_mod_cast hnat
    exact (le_max_left (-b) 0).trans (hceil.trans hNq)
  refine (Asymptotics.IsBigOWith.of_bound (c := C) ?_).isBigO
  have hlt : ∀ᶠ x : ℝ in 𝓝[>] 0, x < 1 :=
    Filter.Eventually.filter_mono inf_le_left
      (Iio_mem_nhds one_pos)
  filter_upwards [self_mem_nhdsWithin, hlt] with x hxpos hxone
  have hsmall := deningerMeyerSum_small_bound f hf N hxpos
  have hsmall' :
      ‖deningerMeyerSum f x‖ ≤ C * x ^ q := by
    simpa [C, q] using hsmall
  have hrpow :
      x ^ (q : ℝ) ≤ x ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_ge hxpos hxone.le hbq
  have hrewrite : x ^ q = x ^ (q : ℝ) := by
    rw [Real.rpow_natCast]
  rw [show ‖x ^ (-b)‖ = x ^ (-b) by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hxpos.le _)]]
  exact hsmall'.trans (by
    rw [hrewrite]
    exact mul_le_mul_of_nonneg_left hrpow hC)

/--
Every source-derived Poisson sum lies in the necessary value-level two-ended
rapid-decay class.
-/
theorem rapidDecayRay_deningerMeyerSum
    (f : SchwartzMap ℝ ℂ) (hf : f ∈ DeningerMeyerCap) :
    RapidDecayRay (deningerMeyerSum f) where
  contOn := continuousOn_deningerMeyerSum f
  decayTop := deningerMeyerSum_isBigO_atTop f hf
  decayZero := deningerMeyerSum_isBigO_zero f hf

/-! ## Linear structure and faithful positive-ray model -/

theorem rapidDecayRay_zero :
    RapidDecayRay (0 : ℝ → ℂ) where
  contOn := continuous_zero.continuousOn
  decayTop := fun a =>
    Asymptotics.isBigO_zero (fun x : ℝ => x ^ (-a)) atTop
  decayZero := fun b =>
    Asymptotics.isBigO_zero (fun x : ℝ => x ^ (-b)) (𝓝[>] 0)

theorem RapidDecayRay.add {g h : ℝ → ℂ}
    (hg : RapidDecayRay g) (hh : RapidDecayRay h) :
    RapidDecayRay (g + h) where
  contOn := hg.contOn.add hh.contOn
  decayTop := fun a => (hg.decayTop a).add (hh.decayTop a)
  decayZero := fun b => (hg.decayZero b).add (hh.decayZero b)

theorem RapidDecayRay.smul (c : ℂ) {g : ℝ → ℂ}
    (hg : RapidDecayRay g) :
    RapidDecayRay (c • g) where
  contOn := by
    change ContinuousOn (fun x => c * g x) (Ioi 0)
    exact continuousOn_const.mul hg.contOn
  decayTop := fun a => (hg.decayTop a).const_smul_left c
  decayZero := fun b => (hg.decayZero b).const_smul_left c

/-- Rapid decay depends only on the restriction to the positive ray. -/
theorem RapidDecayRay.congr_positive {g h : ℝ → ℂ}
    (heq : ∀ x, 0 < x → g x = h x)
    (hh : RapidDecayRay h) :
    RapidDecayRay g where
  contOn := hh.contOn.congr fun x hx => heq x hx
  decayTop := fun a => by
    apply (hh.decayTop a).congr'
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact (heq x hx).symm
    · exact Filter.Eventually.of_forall fun _ => rfl
  decayZero := fun b => by
    apply (hh.decayZero b).congr'
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact (heq x hx).symm
    · exact Filter.Eventually.of_forall fun _ => rfl

/-- Extension of a positive-ray function by zero on the nonpositive axis. -/
def deningerMeyerPositiveExtension (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0 < x then g x else 0

@[simp]
theorem deningerMeyerPositiveExtension_of_pos
    (g : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    deningerMeyerPositiveExtension g x = g x := by
  simp [deningerMeyerPositiveExtension, hx]

@[simp]
theorem deningerMeyerPositiveExtension_of_nonpos
    (g : ℝ → ℂ) {x : ℝ} (hx : x ≤ 0) :
    deningerMeyerPositiveExtension g x = 0 := by
  simp [deningerMeyerPositiveExtension, not_lt.mpr hx]

theorem rapidDecayRay_deningerMeyerPositiveExtension
    {g : ℝ → ℂ} (hg : RapidDecayRay g) :
  RapidDecayRay (deningerMeyerPositiveExtension g) :=
  RapidDecayRay.congr_positive
    (fun _ hx => deningerMeyerPositiveExtension_of_pos g hx) hg

/--
Positive-ray value target.  Zero support on `(-∞,0]` prevents an artificial
negative-support sector, but the target still omits derivative seminorms.
-/
def DeningerMeyerRapidTarget : Submodule ℂ (ℝ → ℂ) where
  carrier := {g |
    RapidDecayRay g ∧ ∀ x : ℝ, x ≤ 0 → g x = 0}
  zero_mem' :=
    ⟨rapidDecayRay_zero, fun _ _ => rfl⟩
  add_mem' := by
    rintro g h ⟨hg, hg0⟩ ⟨hh, hh0⟩
    refine ⟨hg.add hh, fun x hx => ?_⟩
    simp [hg0 x hx, hh0 x hx]
  smul_mem' := by
    rintro c g ⟨hg, hg0⟩
    refine ⟨hg.smul c, fun x hx => ?_⟩
    simp [hg0 x hx]

theorem mem_deningerMeyerRapidTarget_iff (g : ℝ → ℂ) :
    g ∈ DeningerMeyerRapidTarget ↔
      RapidDecayRay g ∧ ∀ x : ℝ, x ≤ 0 → g x = 0 :=
  Iff.rfl

/-- Actual Poisson operator from Meyer's source into the value-level rapid target. -/
def deningerMeyerRapidSumLM :
    DeningerMeyerCap →ₗ[ℂ] DeningerMeyerRapidTarget where
  toFun f :=
    ⟨deningerMeyerPositiveExtension (deningerMeyerSum f),
      (mem_deningerMeyerRapidTarget_iff _).2
        ⟨rapidDecayRay_deningerMeyerPositiveExtension
            (rapidDecayRay_deningerMeyerSum f f.property),
          fun x hx =>
            deningerMeyerPositiveExtension_of_nonpos _ hx⟩⟩
  map_add' f g := by
    apply Subtype.ext
    change deningerMeyerPositiveExtension
        (deningerMeyerSum (↑(f + g) : SchwartzMap ℝ ℂ)) =
      deningerMeyerPositiveExtension
          (deningerMeyerSum (↑f : SchwartzMap ℝ ℂ)) +
        deningerMeyerPositiveExtension
          (deningerMeyerSum (↑g : SchwartzMap ℝ ℂ))
    funext x
    by_cases hx : 0 < x
    · simp only [deningerMeyerPositiveExtension_of_pos _ hx,
        Pi.add_apply]
      exact (deningerMeyerPositiveSumLM x hx.ne').map_add f g
    · simp [deningerMeyerPositiveExtension, hx]
  map_smul' c f := by
    apply Subtype.ext
    change deningerMeyerPositiveExtension
        (deningerMeyerSum (↑(c • f) : SchwartzMap ℝ ℂ)) =
      c • deningerMeyerPositiveExtension
        (deningerMeyerSum (↑f : SchwartzMap ℝ ℂ))
    funext x
    by_cases hx : 0 < x
    · simp only [deningerMeyerPositiveExtension_of_pos _ hx,
        Pi.smul_apply]
      exact (deningerMeyerPositiveSumLM x hx.ne').map_smul c f
    · simp [deningerMeyerPositiveExtension, hx]

@[simp]
theorem deningerMeyerRapidSumLM_apply_pos
    (f : DeningerMeyerCap) {x : ℝ} (hx : 0 < x) :
    ((deningerMeyerRapidSumLM f :
        DeningerMeyerRapidTarget) : ℝ → ℂ) x =
      deningerMeyerSum f x :=
  deningerMeyerPositiveExtension_of_pos _ hx

@[simp]
theorem deningerMeyerRapidSumLM_apply_nonpos
    (f : DeningerMeyerCap) {x : ℝ} (hx : x ≤ 0) :
    ((deningerMeyerRapidSumLM f :
        DeningerMeyerRapidTarget) : ℝ → ℂ) x = 0 :=
  deningerMeyerPositiveExtension_of_nonpos _ hx

/-! ## Value-level quotient proxy -/

/-- Algebraic Meyer middle cohomology `H⁻ / Z(H∩)` with the actual source and target. -/
abbrev DeningerMeyerRapidCohomology :=
  DeningerMeyerRapidTarget ⧸
    LinearMap.range deningerMeyerRapidSumLM

/-- Quotient projection to the value-level cohomology proxy. -/
def deningerMeyerRapidCohomologyClass :
    DeningerMeyerRapidTarget →ₗ[ℂ] DeningerMeyerRapidCohomology :=
  Submodule.mkQ (LinearMap.range deningerMeyerRapidSumLM)

/-- Every actual Poisson boundary has zero class in the value-level proxy. -/
@[simp]
theorem deningerMeyerRapidCohomologyClass_boundary
    (f : DeningerMeyerCap) :
    deningerMeyerRapidCohomologyClass
        (deningerMeyerRapidSumLM f) = 0 := by
  change Submodule.Quotient.mk
    (p := LinearMap.range deningerMeyerRapidSumLM)
      (deningerMeyerRapidSumLM f) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨f, rfl⟩

end

end RHTower
