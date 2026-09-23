import GaloisForLFunctions.RHTower.HedenmalmThetaMobiusHyperbolicRapidity
import GaloisForLFunctions.RHTower.MobiusCriticalClockMoments

/-!
# Pole-unit transverse curvature of the normalized Möbius source

P-G40 identifies the critical normalized source curve with one universal horizontal-boost orbit.
This module extracts the first coefficient that is not fixed by that orbit.

At every finite Euler parameter, the square of the actual normalized source inner product is the
three-point squarefree-partition Gram.  Removing the pole from `ζ(s)/ζ(2s)` factors this Gram into
the universal P-G38 Hardy kernel and a regular arithmetic quotient.  The regular quotient has no
linear midpoint defect.  Its exact quadratic defect is the transverse square `(x-z)^(2 : ℕ)` times the
derivative of the regular squarefree current.

This is an unconditional discriminator, not an RH proof: it identifies and orients the first
arithmetic breaking of the common P/R boost orbit, but does not force the transverse square to
vanish.
-/

open Complex Filter Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Analytic squarefree pole unit `((s-1)ζ(s))/ζ(2s)`. -/
def squarefreeMobiusCriticalPoleUnit (s : ℂ) : ℂ :=
  zetaResidueUnit s / riemannZeta (2 * s)

/-- Regular logarithmic current of the squarefree pole unit. -/
def squarefreeMobiusCriticalRegularCurrent (s : ℂ) : ℂ :=
  -logDeriv squarefreeMobiusCriticalPoleUnit s

/-- Squared finite three-point Gram of the squarefree partition. -/
def squarefreeMobiusFiniteUnitHardyGramSq (epsilon x z : ℂ) : ℂ :=
  let y := (x + z) / 2
  _root_.GaloisForLFunctions.squarefreePartition (1 + y * epsilon) ^ (2 : ℕ) /
    (_root_.GaloisForLFunctions.squarefreePartition (1 + x * epsilon) *
      _root_.GaloisForLFunctions.squarefreePartition (1 + z * epsilon))

/-- Regular arithmetic correction to the universal critical Hardy Gram. -/
def squarefreeMobiusPoleUnitCorrection (epsilon x z : ℂ) : ℂ :=
  let y := (x + z) / 2
  squarefreeMobiusCriticalPoleUnit (1 + y * epsilon) ^ (2 : ℕ) /
    (squarefreeMobiusCriticalPoleUnit (1 + x * epsilon) *
      squarefreeMobiusCriticalPoleUnit (1 + z * epsilon))

/-- Division-free midpoint defect of the pole-unit correction. -/
def squarefreeMobiusPoleUnitMidpointDefect (x z epsilon : ℂ) : ℂ :=
  squarefreeMobiusCriticalPoleUnit (1 + ((x + z) / 2) * epsilon) ^ (2 : ℕ) -
    squarefreeMobiusCriticalPoleUnit (1 + x * epsilon) *
      squarefreeMobiusCriticalPoleUnit (1 + z * epsilon)

/-- Off the pole, the analytic unit is exactly `(s-1)` times the squarefree partition. -/
theorem squarefreeMobiusCriticalPoleUnit_eq_sub_one_mul_squarefreePartition
    {s : ℂ} (hs : s ≠ 1) :
    squarefreeMobiusCriticalPoleUnit s =
      (s - 1) * _root_.GaloisForLFunctions.squarefreePartition s := by
  unfold squarefreeMobiusCriticalPoleUnit
    _root_.GaloisForLFunctions.squarefreePartition
  rw [zetaResidueUnit, Function.update_of_ne hs]
  ring

/-- **Exact finite pole-unit factorization.**  The finite squarefree Gram is the universal
P-G38 kernel `xz/y²` times a regular arithmetic correction. -/
theorem squarefreeMobiusFiniteUnitHardyGramSq_eq_universal_mul_poleUnitCorrection
    {epsilon x z : ℂ} (hepsilon : epsilon ≠ 0) (hx : x ≠ 0) (hz : z ≠ 0)
    (hy : (x + z) / 2 ≠ 0) :
    squarefreeMobiusFiniteUnitHardyGramSq epsilon x z =
      x * z / (((x + z) / 2) ^ (2 : ℕ)) *
        squarefreeMobiusPoleUnitCorrection epsilon x z := by
  let y := (x + z) / 2
  have hxe : x * epsilon ≠ 0 := mul_ne_zero hx hepsilon
  have hze : z * epsilon ≠ 0 := mul_ne_zero hz hepsilon
  have hy0 : y ≠ 0 := by simpa [y] using hy
  have hye : y * epsilon ≠ 0 := mul_ne_zero hy0 hepsilon
  have hxarg : 1 + x * epsilon ≠ 1 := by
    intro h
    apply hxe
    have h' := congrArg (fun w : ℂ => w - 1) h
    simpa using h'
  have hzarg : 1 + z * epsilon ≠ 1 := by
    intro h
    apply hze
    have h' := congrArg (fun w : ℂ => w - 1) h
    simpa using h'
  have hyarg : 1 + y * epsilon ≠ 1 := by
    intro h
    apply hye
    have h' := congrArg (fun w : ℂ => w - 1) h
    simpa using h'
  have hFx :=
    squarefreeMobiusCriticalPoleUnit_eq_sub_one_mul_squarefreePartition hxarg
  have hFz :=
    squarefreeMobiusCriticalPoleUnit_eq_sub_one_mul_squarefreePartition hzarg
  have hFy :=
    squarefreeMobiusCriticalPoleUnit_eq_sub_one_mul_squarefreePartition hyarg
  change _root_.GaloisForLFunctions.squarefreePartition (1 + y * epsilon) ^ (2 : ℕ) /
      (_root_.GaloisForLFunctions.squarefreePartition (1 + x * epsilon) *
        _root_.GaloisForLFunctions.squarefreePartition (1 + z * epsilon)) = _
  change _ = x * z / y ^ (2 : ℕ) *
    (squarefreeMobiusCriticalPoleUnit (1 + y * epsilon) ^ (2 : ℕ) /
      (squarefreeMobiusCriticalPoleUnit (1 + x * epsilon) *
        squarefreeMobiusCriticalPoleUnit (1 + z * epsilon)))
  rw [hFx, hFz, hFy]
  simp only [add_sub_cancel_left]
  field_simp [hx, hz, hy0, hepsilon]

/-- **Literal-source weld.**  For every finite `σ>1`, square of the actual normalized two-aperture
source inner product is the finite squarefree-partition Gram at the three forced affine rates. -/
theorem inner_infiniteMobiusCriticalTwoSidedUnitSignedWeightLp_sq_eq_finiteUnitHardyGramSq
    {sigma u v : ℝ} (hsigma : 1 < sigma)
    (hu : -(1 / 2 : ℝ) < u) (hv : -(1 / 2 : ℝ) < v) :
    inner ℂ
        (infiniteMobiusCriticalTwoSidedUnitSignedWeightLp sigma u hsigma hu)
        (infiniteMobiusCriticalTwoSidedUnitSignedWeightLp sigma v hsigma hv) ^ (2 : ℕ) =
      squarefreeMobiusFiniteUnitHardyGramSq
        (sigma - 1) (1 + 2 * u) (1 + 2 * v) := by
  let sx := mobiusCriticalBoundaryParameter sigma (2 * u)
  let sz := mobiusCriticalBoundaryParameter sigma (2 * v)
  let sy := mobiusCriticalBoundaryParameter sigma (u + v)
  have hsx : 1 < sx := by
    dsimp [sx, mobiusCriticalBoundaryParameter]
    nlinarith
  have hsz : 1 < sz := by
    dsimp [sz, mobiusCriticalBoundaryParameter]
    nlinarith
  have hsy : 1 < sy := by
    dsimp [sy, mobiusCriticalBoundaryParameter]
    nlinarith
  have hsigZ : (squarefreeMobiusTotal sigma : ℂ) =
      _root_.GaloisForLFunctions.squarefreePartition sigma := by
    simpa [_root_.GaloisForLFunctions.squarefreePartition] using
      ofReal_squarefreeMobiusTotal_eq_zetaRatio hsigma
  have hsxZ : (squarefreeMobiusTotal sx : ℂ) =
      _root_.GaloisForLFunctions.squarefreePartition sx := by
    simpa [_root_.GaloisForLFunctions.squarefreePartition] using
      ofReal_squarefreeMobiusTotal_eq_zetaRatio hsx
  have hszZ : (squarefreeMobiusTotal sz : ℂ) =
      _root_.GaloisForLFunctions.squarefreePartition sz := by
    simpa [_root_.GaloisForLFunctions.squarefreePartition] using
      ofReal_squarefreeMobiusTotal_eq_zetaRatio hsz
  have hsyZ : (squarefreeMobiusTotal sy : ℂ) =
      _root_.GaloisForLFunctions.squarefreePartition sy := by
    simpa [_root_.GaloisForLFunctions.squarefreePartition] using
      ofReal_squarefreeMobiusTotal_eq_zetaRatio hsy
  rw [inner_infiniteMobiusCriticalTwoSidedUnitSignedWeightLp hsigma hu hv]
  have hNu := mobiusCriticalTwoSidedUnitNormalization_sq hsigma hu
  have hNv := mobiusCriticalTwoSidedUnitNormalization_sq hsigma hv
  change (((mobiusCriticalTwoSidedUnitNormalization sigma u : ℂ) *
    (mobiusCriticalTwoSidedUnitNormalization sigma v : ℂ) *
      ((squarefreeMobiusTotal sy : ℂ) / (squarefreeMobiusTotal sigma : ℂ))) ^ (2 : ℕ)) = _
  simp only [mul_pow]
  rw [show (mobiusCriticalTwoSidedUnitNormalization sigma u : ℂ) ^ (2 : ℕ) =
      (squarefreeMobiusTotal sigma : ℂ) / (squarefreeMobiusTotal sx : ℂ) by
        exact_mod_cast hNu,
    show (mobiusCriticalTwoSidedUnitNormalization sigma v : ℂ) ^ (2 : ℕ) =
      (squarefreeMobiusTotal sigma : ℂ) / (squarefreeMobiusTotal sz : ℂ) by
        exact_mod_cast hNv]
  rw [hsigZ, hsxZ, hszZ, hsyZ]
  simp only [squarefreeMobiusFiniteUnitHardyGramSq]
  have hsxEq : (sx : ℂ) =
      1 + (1 + 2 * (u : ℂ)) * ((sigma : ℂ) - 1) := by
    dsimp [sx, mobiusCriticalBoundaryParameter]
    push_cast
    ring
  have hszEq : (sz : ℂ) =
      1 + (1 + 2 * (v : ℂ)) * ((sigma : ℂ) - 1) := by
    dsimp [sz, mobiusCriticalBoundaryParameter]
    push_cast
    ring
  have hsyEq : (sy : ℂ) =
      1 + ((1 + 2 * (u : ℂ) + (1 + 2 * (v : ℂ))) / 2) *
        ((sigma : ℂ) - 1) := by
    dsimp [sy, mobiusCriticalBoundaryParameter]
    push_cast
    ring
  rw [← hsxEq, ← hszEq, ← hsyEq]
  have hsig0 :
      _root_.GaloisForLFunctions.squarefreePartition (sigma : ℂ) ≠ 0 :=
    _root_.GaloisForLFunctions.squarefreePartition_ne_zero (by simpa using hsigma)
  have hsx0 : _root_.GaloisForLFunctions.squarefreePartition (sx : ℂ) ≠ 0 :=
    _root_.GaloisForLFunctions.squarefreePartition_ne_zero (by simpa using hsx)
  have hsz0 : _root_.GaloisForLFunctions.squarefreePartition (sz : ℂ) ≠ 0 :=
    _root_.GaloisForLFunctions.squarefreePartition_ne_zero (by simpa using hsz)
  field_simp [hsig0, hsx0, hsz0]

/-- The squarefree pole unit is analytic at the Euler pole. -/
theorem squarefreeMobiusCriticalPoleUnit_analyticAt_one :
    AnalyticAt ℂ squarefreeMobiusCriticalPoleUnit 1 := by
  have hden : AnalyticAt ℂ (fun s : ℂ => riemannZeta (2 * s)) 1 :=
    (analyticOn_riemannZeta (2 * (1 : ℂ)) (by norm_num)).comp (by fun_prop)
  have hdenne : riemannZeta (2 * (1 : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  exact zetaResidueUnit_analyticAt.div hden hdenne

@[simp] theorem squarefreeMobiusCriticalPoleUnit_one :
    squarefreeMobiusCriticalPoleUnit 1 = 1 / riemannZeta 2 := by
  simp [squarefreeMobiusCriticalPoleUnit, zetaResidueUnit_one]

theorem squarefreeMobiusCriticalPoleUnit_one_ne_zero :
    squarefreeMobiusCriticalPoleUnit 1 ≠ 0 := by
  rw [squarefreeMobiusCriticalPoleUnit_one]
  exact div_ne_zero one_ne_zero (riemannZeta_ne_zero_of_one_lt_re (by norm_num))

/-- The regular squarefree current is analytic at the Euler pole. -/
theorem squarefreeMobiusCriticalRegularCurrent_analyticAt_one :
    AnalyticAt ℂ squarefreeMobiusCriticalRegularCurrent 1 := by
  change AnalyticAt ℂ
    (fun z => -(deriv squarefreeMobiusCriticalPoleUnit z /
      squarefreeMobiusCriticalPoleUnit z)) 1
  exact (squarefreeMobiusCriticalPoleUnit_analyticAt_one.deriv.div
    squarefreeMobiusCriticalPoleUnit_analyticAt_one
    squarefreeMobiusCriticalPoleUnit_one_ne_zero).neg

/-- Exact pole/Euler decomposition of the public regular current. -/
theorem squarefreeMobiusCriticalRegularCurrent_eq_pole_sub_euler
    {s : ℂ} (hs : (1 / 2 : ℝ) < s.re) (hG : zetaResidueUnit s ≠ 0) :
    squarefreeMobiusCriticalRegularCurrent s =
      -logDeriv zetaResidueUnit s - 2 * infinitePrimeFlux (2 * s) := by
  have h2re : 1 < (2 * s).re := by
    norm_num only [mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have h2one : 2 * s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num only [mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero,
      one_re] at hre
    linarith
  have hdenne : riemannZeta (2 * s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re h2re
  have hdenDiff : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (2 * z)) s :=
    (differentiableAt_riemannZeta h2one).comp s (by fun_prop)
  have hdiv := logDeriv_div s hG hdenne
    (analyticAt_zetaResidueUnit s).differentiableAt hdenDiff
  change logDeriv squarefreeMobiusCriticalPoleUnit s = _ at hdiv
  have hchain := logDeriv_comp (f := riemannZeta) (g := fun z : ℂ => 2 * z)
    (differentiableAt_riemannZeta h2one)
    (show DifferentiableAt ℂ (fun z : ℂ => 2 * z) s by fun_prop)
  change logDeriv (fun z : ℂ => riemannZeta (2 * z)) s =
    logDeriv riemannZeta (2 * s) * deriv (fun z : ℂ => 2 * z) s at hchain
  have hderiv : deriv (fun z : ℂ => 2 * z) s = 2 := by simp
  rw [hderiv] at hchain
  unfold squarefreeMobiusCriticalRegularCurrent infinitePrimeFlux
  rw [hdiv]
  linear_combination hchain

/-- Derivative-level pole/Euler curvature split at `s=1`. -/
theorem deriv_squarefreeMobiusCriticalRegularCurrent_eq_pole_curvature_add_euler_curvature :
    deriv squarefreeMobiusCriticalRegularCurrent 1 =
      -deriv (logDeriv zetaResidueUnit) 1 - 4 * deriv infinitePrimeFlux 2 := by
  have heq : squarefreeMobiusCriticalRegularCurrent =ᶠ[nhds (1 : ℂ)]
      fun s => -logDeriv zetaResidueUnit s - 2 * infinitePrimeFlux (2 * s) := by
    filter_upwards [
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (1 / 2 : ℝ) < ((1 : ℂ)).re by norm_num),
      zetaResidueUnit_ne_zero_eventually] with s hs hG
    exact squarefreeMobiusCriticalRegularCurrent_eq_pole_sub_euler hs hG
  rw [heq.deriv_eq]
  have hpole : DifferentiableAt ℂ (logDeriv zetaResidueUnit) 1 := by
    have hGne : zetaResidueUnit 1 ≠ 0 := by simp [zetaResidueUnit_one]
    rw [show logDeriv zetaResidueUnit =
        fun z => deriv zetaResidueUnit z / zetaResidueUnit z by
      funext z
      rw [logDeriv_apply]]
    exact (zetaResidueUnit_analyticAt.deriv.div zetaResidueUnit_analyticAt
      hGne).differentiableAt
  have hfluxComp :
      DifferentiableAt ℂ (fun s : ℂ => infinitePrimeFlux (2 * s)) 1 :=
    _root_.GaloisForLFunctions.differentiableAt_infinitePrimeFlux_two_mul
      (by norm_num)
  have hflux : DifferentiableAt ℂ infinitePrimeFlux 2 := by
    unfold infinitePrimeFlux
    rw [show (fun z => -logDeriv riemannZeta z) =
        fun z => -deriv riemannZeta z / riemannZeta z by
      funext z
      rw [logDeriv_apply]
      ring]
    exact differentiableAt_neg_logDeriv_riemannZeta_of_one_lt_re
      (s := (2 : ℂ)) (by norm_num)
  have hchain : deriv (fun s : ℂ => infinitePrimeFlux (2 * s)) 1 =
      deriv infinitePrimeFlux 2 * 2 := by
    have haff : HasDerivAt (fun s : ℂ => 2 * s) 2 1 := by
      convert! ((hasDerivAt_id (𝕜 := ℂ) (x := (1 : ℂ))).const_mul 2) using 1
      all_goals ring
    have hflux' : HasDerivAt infinitePrimeFlux
        (deriv infinitePrimeFlux 2) (2 * (1 : ℂ)) := by
      simpa using hflux.hasDerivAt
    change deriv (infinitePrimeFlux ∘ fun s : ℂ => 2 * s) 1 = _
    exact (hflux'.comp 1 haff).deriv
  have hsub := deriv_sub hpole.neg (hfluxComp.const_mul 2)
  change deriv (fun s : ℂ => -logDeriv zetaResidueUnit s -
      2 * infinitePrimeFlux (2 * s)) 1 = _ at hsub
  rw [hsub]
  have hneg := hpole.hasDerivAt.neg.deriv
  change deriv (fun s : ℂ => -logDeriv zetaResidueUnit s) 1 = _ at hneg
  have hneg' : deriv (-logDeriv zetaResidueUnit) 1 =
      -deriv (logDeriv zetaResidueUnit) 1 := hneg
  have hconst := deriv_const_mul 2 hfluxComp
  change deriv (fun s : ℂ => 2 * infinitePrimeFlux (2 * s)) 1 = _ at hconst
  rw [hneg', hconst, hchain]
  ring

private def analyticMidpointDefect (f : ℂ → ℂ) (x z epsilon : ℂ) : ℂ :=
  f (1 + ((x + z) / 2) * epsilon) ^ (2 : ℕ) -
    f (1 + x * epsilon) * f (1 + z * epsilon)

private theorem analyticMidpointDefect_iteratedDeriv_two
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 1) (x z : ℂ) :
    iteratedDeriv 2 (analyticMidpointDefect f x z) 0 =
      ((x - z) ^ (2 : ℕ) / 2) *
        ((deriv f 1) ^ (2 : ℕ) - f 1 * deriv (deriv f) 1) := by
  let h : ℂ → ℂ → ℂ := fun a => f ∘ fun epsilon => 1 + a * epsilon
  have hcont (a : ℂ) : ContDiffAt ℂ 2 (h a) 0 := by
    have hf' : ContDiffAt ℂ 2 f (1 + a * (0 : ℂ)) := by
      simpa using (hf.contDiffAt : ContDiffAt ℂ 2 f 1)
    exact hf'.comp 0 (by fun_prop)
  have hval (a : ℂ) : h a 0 = f 1 := by simp [h]
  have hderiv (a : ℂ) : deriv (h a) 0 = deriv f 1 * a := by
    have haff : HasDerivAt (fun epsilon : ℂ => 1 + a * epsilon) a 0 := by
      convert! (hasDerivAt_const (x := (0 : ℂ)) (c := (1 : ℂ))).add
        ((hasDerivAt_id (𝕜 := ℂ) (x := 0)).const_mul a) using 1
      all_goals ring
    have hf' : HasDerivAt f (deriv f 1) (1 + a * (0 : ℂ)) := by
      simpa using hf.differentiableAt.hasDerivAt
    change deriv (f ∘ fun epsilon : ℂ => 1 + a * epsilon) 0 = _
    exact (hf'.comp 0 haff).deriv
  have hsecond (a : ℂ) :
      iteratedDeriv 2 (h a) 0 = iteratedDeriv 2 f 1 * a ^ (2 : ℕ) := by
    have hf' : ContDiffAt ℂ 2 f (1 + a * (0 : ℂ)) := by
      simpa using (hf.contDiffAt : ContDiffAt ℂ 2 f 1)
    have hc := iteratedDeriv_comp_two (g := f)
      (f := fun epsilon : ℂ => 1 + a * epsilon) hf'
      (by fun_prop : ContDiffAt ℂ 2 (fun epsilon : ℂ => 1 + a * epsilon) 0)
    change iteratedDeriv 2 (h a) 0 = _ at hc
    rw [hc]
    have haffDeriv : deriv (fun epsilon : ℂ => 1 + a * epsilon) 0 = a := by
      convert! ((hasDerivAt_const (x := (0 : ℂ)) (c := (1 : ℂ))).add
        ((hasDerivAt_id (𝕜 := ℂ) (x := 0)).const_mul a)).deriv using 1
      all_goals ring
    have haffSecond :
        iteratedDeriv 2 (fun epsilon : ℂ => 1 + a * epsilon) 0 = 0 := by
      rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
      have heq : deriv (fun epsilon : ℂ => 1 + a * epsilon) = fun _ => a := by
        funext epsilon
        convert! ((hasDerivAt_const (x := epsilon) (c := (1 : ℂ))).add
          ((hasDerivAt_id (𝕜 := ℂ) (x := epsilon)).const_mul a)).deriv using 1
        all_goals ring
      rw [heq]
      simp
    rw [haffDeriv, haffSecond]
    ring
  have hzero (a : ℂ) : iteratedDeriv 0 (h a) 0 = f 1 := by
    rw [iteratedDeriv_zero]
    exact hval a
  have hone (a : ℂ) : iteratedDeriv 1 (h a) 0 = deriv f 1 * a := by
    rw [iteratedDeriv_one]
    exact hderiv a
  have hsub := iteratedDeriv_sub (n := 2) (x := (0 : ℂ))
    ((hcont ((x + z) / 2)).mul (hcont ((x + z) / 2)))
    ((hcont x).mul (hcont z))
  have hdef : analyticMidpointDefect f x z =
      (h ((x + z) / 2) * h ((x + z) / 2)) - (h x * h z) := by
    funext epsilon
    simp [analyticMidpointDefect, h, Function.comp_def, pow_two]
  rw [hdef]
  change iteratedDeriv 2
    ((fun epsilon => h ((x + z) / 2) epsilon * h ((x + z) / 2) epsilon) -
      (fun epsilon => h x epsilon * h z epsilon)) 0 = _
  have hmulyy := iteratedDeriv_mul
    (hcont ((x + z) / 2)) (hcont ((x + z) / 2))
  change iteratedDeriv 2
    (fun epsilon => h ((x + z) / 2) epsilon * h ((x + z) / 2) epsilon) 0 =
      _ at hmulyy
  have hmulxz := iteratedDeriv_mul (hcont x) (hcont z)
  change iteratedDeriv 2 (fun epsilon => h x epsilon * h z epsilon) 0 = _ at hmulxz
  rw [hsub, hmulyy, hmulxz]
  simp only [Finset.sum_range_succ, Nat.choose_zero_right, Nat.cast_one,
    one_mul, Nat.choose_self, Nat.cast_ofNat, Nat.choose_one_right,
    hzero, hone, hsecond]
  rw [show iteratedDeriv 2 f 1 = deriv (deriv f) 1 by
    rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
  ring

/-- Quotient differentiation converts the Laguerre numerator into regular-current curvature. -/
theorem deriv_squarefreeMobiusCriticalRegularCurrent_mul_poleUnit_sq :
    deriv squarefreeMobiusCriticalRegularCurrent 1 *
        squarefreeMobiusCriticalPoleUnit 1 ^ (2 : ℕ) =
      deriv squarefreeMobiusCriticalPoleUnit 1 ^ (2 : ℕ) -
        squarefreeMobiusCriticalPoleUnit 1 *
          deriv (deriv squarefreeMobiusCriticalPoleUnit) 1 := by
  have hquot :=
    squarefreeMobiusCriticalPoleUnit_analyticAt_one.deriv.differentiableAt.hasDerivAt.neg.div
      squarefreeMobiusCriticalPoleUnit_analyticAt_one.differentiableAt.hasDerivAt
      squarefreeMobiusCriticalPoleUnit_one_ne_zero
  have hder : deriv squarefreeMobiusCriticalRegularCurrent 1 =
      ((-deriv (deriv squarefreeMobiusCriticalPoleUnit) 1) *
          squarefreeMobiusCriticalPoleUnit 1 -
        (-deriv squarefreeMobiusCriticalPoleUnit 1) *
          deriv squarefreeMobiusCriticalPoleUnit 1) /
        squarefreeMobiusCriticalPoleUnit 1 ^ (2 : ℕ) := by
    unfold squarefreeMobiusCriticalRegularCurrent
    rw [show (fun s => -logDeriv squarefreeMobiusCriticalPoleUnit s) =
        fun z => -deriv squarefreeMobiusCriticalPoleUnit z /
          squarefreeMobiusCriticalPoleUnit z by
      funext z
      rw [logDeriv_apply]
      ring]
    exact hquot.deriv
  rw [hder]
  rw [div_mul_cancel₀ _
    (pow_ne_zero 2 squarefreeMobiusCriticalPoleUnit_one_ne_zero)]
  ring

/-- P-G41 zeroth-order cancellation. -/
@[simp] theorem squarefreeMobiusPoleUnitMidpointDefect_zero (x z : ℂ) :
    squarefreeMobiusPoleUnitMidpointDefect x z 0 = 0 := by
  simp only [squarefreeMobiusPoleUnitMidpointDefect, mul_zero, add_zero]
  ring

/-- P-G41 first-order cancellation: midpoint centering kills every affine Laurent coefficient. -/
theorem squarefreeMobiusPoleUnitMidpointDefect_iteratedDeriv_one (x z : ℂ) :
    iteratedDeriv 1 (squarefreeMobiusPoleUnitMidpointDefect x z) 0 = 0 := by
  let h : ℂ → ℂ → ℂ := fun a =>
    squarefreeMobiusCriticalPoleUnit ∘ fun epsilon => 1 + a * epsilon
  have hder (a : ℂ) : HasDerivAt (h a)
      (deriv squarefreeMobiusCriticalPoleUnit 1 * a) 0 := by
    have haff : HasDerivAt (fun epsilon : ℂ => 1 + a * epsilon) a 0 := by
      convert! (hasDerivAt_const (x := (0 : ℂ)) (c := (1 : ℂ))).add
        ((hasDerivAt_id (𝕜 := ℂ) (x := 0)).const_mul a) using 1
      all_goals ring
    have hf' : HasDerivAt squarefreeMobiusCriticalPoleUnit
        (deriv squarefreeMobiusCriticalPoleUnit 1) (1 + a * (0 : ℂ)) := by
      simpa using squarefreeMobiusCriticalPoleUnit_analyticAt_one.differentiableAt.hasDerivAt
    exact hf'.comp 0 haff
  have hdef : squarefreeMobiusPoleUnitMidpointDefect x z =
      (h ((x + z) / 2) * h ((x + z) / 2)) - (h x * h z) := by
    funext epsilon
    simp [squarefreeMobiusPoleUnitMidpointDefect, h, Function.comp_def, pow_two]
  rw [iteratedDeriv_one, hdef]
  have hmulY := (hder ((x + z) / 2)).mul (hder ((x + z) / 2))
  have hmulXZ := (hder x).mul (hder z)
  have hsub := hmulY.sub hmulXZ
  change HasDerivAt
    ((fun epsilon => h ((x + z) / 2) epsilon * h ((x + z) / 2) epsilon) -
      (fun epsilon => h x epsilon * h z epsilon)) _ 0 at hsub
  change deriv
    ((fun epsilon => h ((x + z) / 2) epsilon * h ((x + z) / 2) epsilon) -
      (fun epsilon => h x epsilon * h z epsilon)) 0 = _
  rw [hsub.deriv]
  simp [h, Function.comp_def]
  ring

/-- **P-G41 exact transverse arithmetic jet.**  Arithmetic is invisible at orders zero and one;
the first surviving coefficient is the regular-current curvature times the transverse square. -/
theorem squarefreeMobiusPoleUnitMidpointDefect_iteratedDeriv_two (x z : ℂ) :
    iteratedDeriv 2 (squarefreeMobiusPoleUnitMidpointDefect x z) 0 =
      ((x - z) ^ (2 : ℕ) / 2) * squarefreeMobiusCriticalPoleUnit 1 ^ (2 : ℕ) *
        deriv squarefreeMobiusCriticalRegularCurrent 1 := by
  have hgeneric := analyticMidpointDefect_iteratedDeriv_two
    squarefreeMobiusCriticalPoleUnit_analyticAt_one x z
  change iteratedDeriv 2 (analyticMidpointDefect
    squarefreeMobiusCriticalPoleUnit x z) 0 = _
  rw [hgeneric]
  rw [← deriv_squarefreeMobiusCriticalRegularCurrent_mul_poleUnit_sq]
  ring

end

end RHTower.HedenmalmThetaSource
