import GaloisForLFunctions.BlackHoleRingdown.TheRingdownExpansion
import GaloisForLFunctions.BlackHoleRingdown.TheCausalSymbolOfTheModularHorizon

/-!
# The modes of the ringdown

The residues in the ringdown expansion are the modes of the black hole.

* At a zero of multiplicity `n + 1` the residue is `e^{pτ}` times a polynomial in `τ` of degree at most
  `n`, for any multiplicity. No simplicity of the zeros is used.
* The top coefficient vanishes only where the numerator `N(p; x, Y)` vanishes, and the horocycle mean of
  `N(p; ·, Y)` is the nonzero number `((1+2p)/(2p-1)) ξ(2p) Y^{½-p}`. So every zero is excited.
* After the lift of decay `D` a mode oscillates as `e^{-iωτ}` with `ω = i(p - D)`. This is the minus
  branch of the quasinormal spectrum, at rate `D - Re p = D + (1-β)/2` and frequency `-γ/2`. A plus
  branch frequency is never a mode frequency, because the poles lie in `Re p < 0`.
* The Neumann and Dirichlet fields on the black hole inherit the expansion.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower HTGeometry

/-! ### The residue against an exponential, at any multiplicity -/

/-- Leibniz rule for the Taylor coefficients of `H(t) c e^{τt}`. -/
theorem taylorCoeffZero_mul_exp {H : ℂ → ℂ} (hH : AnalyticAt ℂ H 0) (c τ : ℂ) (n : ℕ) :
    taylorCoeffZero (fun t => H t * (c * Complex.exp (τ * t))) n =
      c * ∑ i ∈ Finset.range (n + 1),
        taylorCoeffZero H i * τ ^ (n - i) / ((n - i).factorial : ℂ) := by
  have hE : AnalyticAt ℂ (fun t : ℂ => c * Complex.exp (τ * t)) 0 := by fun_prop
  have hL : iteratedDeriv n (fun t => H t * (c * Complex.exp (τ * t))) 0 =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * iteratedDeriv i H 0 *
        iteratedDeriv (n - i) (fun t : ℂ => c * Complex.exp (τ * t)) 0 :=
    iteratedDeriv_mul (n := n) (x := (0 : ℂ)) (f := H)
      (g := fun t : ℂ => c * Complex.exp (τ * t)) hH.contDiffAt hE.contDiffAt
  have hEder : ∀ j : ℕ, iteratedDeriv j (fun t : ℂ => c * Complex.exp (τ * t)) 0 = c * τ ^ j := by
    intro j
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_cexp_const_mul]
    simp
  have hfac : ∀ q : ℕ, ((q.factorial : ℂ)) ≠ 0 := fun q => Nat.cast_ne_zero.mpr q.factorial_ne_zero
  rw [taylorCoeffZero, hL, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [hEder, taylorCoeffZero]
  have hc : ((n.choose i : ℂ)) * ((i.factorial : ℂ)) * (((n - i).factorial : ℂ)) =
      ((n.factorial : ℂ)) := by
    exact_mod_cast congrArg (Nat.cast (R := ℂ)) (Nat.choose_mul_factorial_mul_factorial hin)
  rw [div_eq_iff (hfac n), ← hc]
  have h1 := hfac i
  have h2 := hfac (n - i)
  have hcancel : iteratedDeriv i H 0 / (i.factorial : ℂ) * τ ^ (n - i) / ((n - i).factorial : ℂ) *
      ((i.factorial : ℂ) * ((n - i).factorial : ℂ)) = iteratedDeriv i H 0 * τ ^ (n - i) := by
    field_simp
  linear_combination (-(c * (n.choose i : ℂ))) * hcancel

/-- **The residue at a zero of order `n + 1`.**  Against `e^{uτ}`, the quotient `R/D` has residue `e^{pτ}`
times a polynomial in `τ` of degree at most `n`. -/
theorem laurentCoeff_mul_exp_div {R D g : ℂ → ℂ} {p : ℂ} {n : ℕ} (hR : AnalyticAt ℂ R p)
    (hg : AnalyticAt ℂ g p) (hgp : g p ≠ 0)
    (hD : ∀ᶠ z in 𝓝 p, D z = (z - p) ^ (n + 1) • g z) (τ : ℂ) :
    laurentCoeff (fun u => R u * Complex.exp (u * τ) / D u) p (-1) =
      Complex.exp (p * τ) * ∑ i ∈ Finset.range (n + 1),
        taylorCoeffZero (fun t => R (p + t) / g (p + t)) i * τ ^ (n - i) /
          ((n - i).factorial : ℂ) := by
  set H : ℂ → ℂ := fun t => R (p + t) / g (p + t) with hHdef
  have hshift : AnalyticAt ℂ (fun t : ℂ => p + t) 0 := by fun_prop
  have hRt : AnalyticAt ℂ (fun t : ℂ => R (p + t)) 0 := by
    have h : AnalyticAt ℂ R (p + 0) := by simpa using hR
    exact AnalyticAt.fun_comp h hshift
  have hgt : AnalyticAt ℂ (fun t : ℂ => g (p + t)) 0 := by
    have h : AnalyticAt ℂ g (p + 0) := by simpa using hg
    exact AnalyticAt.fun_comp h hshift
  have hg0 : g (p + 0) ≠ 0 := by simpa using hgp
  have hH : AnalyticAt ℂ H 0 := hRt.div hgt hg0
  set E : ℂ → ℂ := fun t => H t * (Complex.exp (p * τ) * Complex.exp (τ * t)) with hE
  have hEan : AnalyticAt ℂ E 0 := hH.mul (by fun_prop)
  set F : ℂ → ℂ := fun u => R u * Complex.exp (u * τ) / D u with hF
  have hev : laurentShift F p (n + 1 + 1) =ᶠ[𝓝 0] fun t => t ^ 1 * E t := by
    have hT : Tendsto (fun t : ℂ => p + t) (𝓝 0) (𝓝 p) := by
      have hc : Continuous (fun t : ℂ => p + t) := by fun_prop
      simpa using hc.tendsto 0
    filter_upwards [hT.eventually hD, hgt.continuousAt.eventually_ne hg0] with t h1 h2
    simp only [add_sub_cancel_left, smul_eq_mul] at h1
    have hexp : Complex.exp ((p + t) * τ) = Complex.exp (p * τ) * Complex.exp (τ * t) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    simp only [laurentShift, hF, hE, hHdef]
    rw [h1, hexp]
    generalize Complex.exp (p * τ) * Complex.exp (τ * t) = X
    by_cases ht : t = 0
    · simp [ht]
    · have ht' : t ^ (n + 1) ≠ 0 := pow_ne_zero _ ht
      rw [pow_succ t (n + 1), pow_one]
      field_simp
  have hana : AnalyticAt ℂ (laurentShift F p (n + 1 + 1)) 0 :=
    ((by fun_prop : AnalyticAt ℂ (fun t : ℂ => t ^ 1) 0).mul hEan).congr hev.symm
  have hval := laurentCoeff_eq_taylorCoeffZero (f := F) (a := p) (k := n + 1 + 1) (ℓ := -1) hana
    (by push_cast; omega)
  have hidx : ((-1 : ℤ) + ((n + 1 + 1 : ℕ) : ℤ)).toNat = n + 1 := by omega
  have hcongr : taylorCoeffZero (laurentShift F p (n + 1 + 1)) (n + 1) =
      taylorCoeffZero (fun t => t ^ 1 * E t) (n + 1) := by
    simp only [taylorCoeffZero]
    rw [hev.iteratedDeriv_eq]
  rw [hval, hidx, hcongr, taylorCoeffZero_pow_mul hEan 1 (n + 1), if_pos (by omega),
    show n + 1 - 1 = n by omega]
  exact taylorCoeffZero_mul_exp hH _ τ n

/-- The factorization of `ξ(1+2u)` at a zero. -/
theorem exists_xi_shift_factor {p : ℂ} (hp : xi (1 + 2 * p) = 0) :
    ∃ (n : ℕ) (g : ℂ → ℂ), analyticOrderAt (fun u : ℂ => xi (1 + 2 * u)) p = ((n + 1 : ℕ) : ℕ∞) ∧
      AnalyticAt ℂ g p ∧ g p ≠ 0 ∧ ∀ᶠ z in 𝓝 p, xi (1 + 2 * z) = (z - p) ^ (n + 1) • g z := by
  have han : AnalyticAt ℂ (fun u : ℂ => xi (1 + 2 * u)) p := differentiable_xi_shift.analyticAt p
  have hnz : xi (1 + 2 * (0 : ℂ)) ≠ 0 := by
    rw [mul_zero, add_zero, xi_one]
    norm_num
  have htop : analyticOrderAt (fun u : ℂ => xi (1 + 2 * u)) p ≠ ⊤ := by
    intro h
    have hevent := analyticOrderAt_eq_top.mp h
    have hglobal : AnalyticOnNhd ℂ (fun u : ℂ => xi (1 + 2 * u)) Set.univ :=
      fun z _ => differentiable_xi_shift.analyticAt z
    have hall := hglobal.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ p) hevent
    exact hnz (hall (Set.mem_univ 0))
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
  obtain ⟨g, hgan, hg0, hfac⟩ := (han.analyticOrderAt_eq_natCast (n := m)).mp hm.symm
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · have hval := hfac.self_of_nhds
    rw [pow_zero, one_smul] at hval
    exact absurd (hval.symm.trans hp) hg0
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    exact ⟨n, g, hm.symm, hgan, hg0, hfac⟩

/-! ### The location of the poles -/

theorem re_neg_of_xi_shift_eq_zero {p : ℂ} (hp : xi (1 + 2 * p) = 0) : p.re < 0 := by
  have h := re_lt_one_of_xi_eq_zero hp
  simp at h
  linarith

theorem re_gt_of_xi_shift_eq_zero {p : ℂ} (hp : xi (1 + 2 * p) = 0) : -(1 / 2) < p.re := by
  have h := re_pos_of_xi_eq_zero hp
  simp at h
  linarith

/-- At a pole, `ξ(2p) ≠ 0`, since `1 - 2p` lies to the right of the line `Re s = 1`. -/
theorem xi_two_mul_ne_zero {p : ℂ} (hp : xi (1 + 2 * p) = 0) : xi (2 * p) ≠ 0 := by
  have hre := re_neg_of_xi_shift_eq_zero hp
  have hsym : xi (2 * p) = xi (1 - 2 * p) := (xi_one_sub (2 * p)).symm
  rw [hsym]
  refine xi_ne_zero_of_one_le_re ?_
  simp
  linarith

/-! ### The mode of a zero -/

/-- The time-free numerator `a(-iu) N(u; x, Y)`. -/
def modeNumerator (ε ξ₀ x Y : ℝ) (u : ℂ) : ℂ :=
  gaussianAmplitude ε ξ₀ (-I * u) * eisensteinNumerator u x Y

theorem inverseXiQuotient_packet_eq (ε ξ₀ τ x Y : ℝ) :
    inverseXiQuotient (packetNumerator ε ξ₀ τ x Y) = fun u =>
      modeNumerator ε ξ₀ x Y u * Complex.exp (u * (τ : ℂ)) / xi (1 + 2 * u) := by
  funext u
  simp only [inverseXiQuotient, packetNumerator, modeNumerator]
  ring

theorem gaussianAmplitude_ne_zero (ε ξ₀ : ℝ) (w : ℂ) : gaussianAmplitude ε ξ₀ w ≠ 0 :=
  Complex.exp_ne_zero _

/-- **The mode of a zero.**  At a zero of `ξ(1+2u)` of multiplicity `n + 1`, the residue of the packet is
`e^{pτ}` times a polynomial in `τ` of degree at most `n`. Its top coefficient vanishes exactly where
`N(p; x, Y)` does. -/
theorem exists_ringdownMode (ε ξ₀ x : ℝ) {Y : ℝ} (hY : 0 < Y) {p : ℂ} (hp : xi (1 + 2 * p) = 0) :
    ∃ (n : ℕ) (c : ℕ → ℂ),
      analyticOrderAt (fun u : ℂ => xi (1 + 2 * u)) p = ((n + 1 : ℕ) : ℕ∞) ∧
      (c 0 = 0 ↔ eisensteinNumerator p x Y = 0) ∧
      ∀ τ : ℝ, laurentCoeff (inverseXiQuotient (packetNumerator ε ξ₀ τ x Y)) p (-1) =
        Complex.exp (p * (τ : ℂ)) * ∑ i ∈ Finset.range (n + 1),
          c i * (τ : ℂ) ^ (n - i) / ((n - i).factorial : ℂ) := by
  obtain ⟨n, g, horder, hg, hg0, hfac⟩ := exists_xi_shift_factor hp
  have hN : AnalyticAt ℂ (modeNumerator ε ξ₀ x Y) p :=
    (analyticAt_gaussianAmplitude_rotated ε ξ₀ p).mul
      (analyticAt_eisensteinNumerator x hY (re_neg_of_xi_shift_eq_zero hp).le)
  refine ⟨n, fun i => taylorCoeffZero (fun t => modeNumerator ε ξ₀ x Y (p + t) / g (p + t)) i,
    horder, ?_, fun τ => ?_⟩
  · simp only [taylorCoeffZero, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      add_zero, modeNumerator, div_eq_zero_iff, hg0, or_false, mul_eq_zero,
      gaussianAmplitude_ne_zero, false_or]
  · rw [inverseXiQuotient_packet_eq]
    exact laurentCoeff_mul_exp_div hN hg hg0 hfac (τ : ℂ)

/-- **The mode of a simple zero.** -/
theorem laurentCoeff_packet_of_simple (ε ξ₀ τ x : ℝ) {Y : ℝ} (hY : 0 < Y) {p : ℂ}
    (hp : xi (1 + 2 * p) = 0) (hd : deriv (fun u : ℂ => xi (1 + 2 * u)) p ≠ 0) :
    laurentCoeff (inverseXiQuotient (packetNumerator ε ξ₀ τ x Y)) p (-1) =
      Complex.exp (p * (τ : ℂ)) * (gaussianAmplitude ε ξ₀ (-I * p) * eisensteinNumerator p x Y /
        deriv (fun u : ℂ => xi (1 + 2 * u)) p) := by
  have han := (gaussianNumerator_packet (ε := 1) one_pos ξ₀ τ x hY le_rfl).analytic
  have hN : AnalyticAt ℂ (packetNumerator ε ξ₀ τ x Y) p := by
    have h1 : AnalyticAt ℂ (fun v : ℂ => Complex.exp (v * (τ : ℂ))) p := by fun_prop
    exact ((analyticAt_gaussianAmplitude_rotated ε ξ₀ p).mul h1).mul
      (analyticAt_eisensteinNumerator x hY (re_neg_of_xi_shift_eq_zero hp).le)
  rw [laurentCoeff_inverseXiQuotient_of_simple hN hp hd, packetNumerator]
  ring

/-! ### Every zero is excited -/

theorem integrableOn_eisTail (u : ℂ) {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun x => eisTail u x Y) (Ioc 0 1) := by
  have hT : ∀ negative : Bool, IntegrableOn (fun x => weightedTail u negative x Y) (Ioc 0 1) := by
    intro negative
    simp_rw [weightedTail_eq_signedSqrtWhittakerTail]
    exact (continuous_signedSqrtWhittakerTail_x negative hY u).integrableOn_Ioc
  exact (hT false).add (hT true)

theorem setIntegral_eisTail (u : ℂ) {Y : ℝ} (hY : 0 < Y) :
    ∫ x in Ioc (0 : ℝ) 1, eisTail u x Y = 0 := by
  have hT : ∀ negative : Bool, IntegrableOn (fun x => weightedTail u negative x Y) (Ioc 0 1) := by
    intro negative
    simp_rw [weightedTail_eq_signedSqrtWhittakerTail]
    exact (continuous_signedSqrtWhittakerTail_x negative hY u).integrableOn_Ioc
  have hZ : ∀ negative : Bool, ∫ x in Ioc (0 : ℝ) 1, weightedTail u negative x Y = 0 := by
    intro negative
    simp_rw [weightedTail_eq_signedSqrtWhittakerTail]
    exact setIntegral_Ioc_signedSqrtWhittakerTail negative hY u
  have hsplit : (∫ x in Ioc (0 : ℝ) 1, eisTail u x Y) =
      (∫ x in Ioc (0 : ℝ) 1, weightedTail u false x Y) +
        ∫ x in Ioc (0 : ℝ) 1, weightedTail u true x Y := integral_add (hT false) (hT true)
  rw [hsplit, hZ, hZ, add_zero]

/-- The horocycle mean of the numerator. -/
theorem setIntegral_eisensteinNumerator (u : ℂ) {Y : ℝ} (hY : 0 < Y) :
    ∫ x in Ioc (0 : ℝ) 1, eisensteinNumerator u x Y =
      (Y : ℂ) ^ (1 / 2 + u) * xi (1 + 2 * u) +
        (1 + 2 * u) / (2 * u - 1) * xi (2 * u) * (Y : ℂ) ^ (1 / 2 - u) := by
  have hfin : volume (Ioc (0 : ℝ) 1) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hconst : IntegrableOn (fun _ : ℝ => (Y : ℂ) ^ (1 / 2 + u) * xi (1 + 2 * u) +
      (1 + 2 * u) / (2 * u - 1) * xi (2 * u) * (Y : ℂ) ^ (1 / 2 - u)) (Ioc 0 1) :=
    integrableOn_const hfin
  have hsplit : (∫ x in Ioc (0 : ℝ) 1, eisensteinNumerator u x Y) =
      (∫ _x in Ioc (0 : ℝ) 1, (Y : ℂ) ^ (1 / 2 + u) * xi (1 + 2 * u) +
        (1 + 2 * u) / (2 * u - 1) * xi (2 * u) * (Y : ℂ) ^ (1 / 2 - u)) +
        ∫ x in Ioc (0 : ℝ) 1, (1 + 2 * u) * (2 * u) * eisTail u x Y :=
    integral_add hconst ((integrableOn_eisTail u hY).const_mul _)
  rw [hsplit, integral_const_mul, setIntegral_eisTail u hY, mul_zero, add_zero, setIntegral_const]
  simp [Measure.real, Real.volume_Ioc]

/-- **Every zero is excited.**  For every height `Y` there is a point of the horocycle where the top
coefficient of the mode of `p` does not vanish: the horocycle mean of the numerator at a pole is the
nonzero constant term `((1+2p)/(2p-1)) ξ(2p) Y^{½-p}`. -/
theorem exists_eisensteinNumerator_ne_zero {p : ℂ} (hp : xi (1 + 2 * p) = 0) {Y : ℝ} (hY : 0 < Y) :
    ∃ x ∈ Ioc (0 : ℝ) 1, eisensteinNumerator p x Y ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hzero : ∫ x in Ioc (0 : ℝ) 1, eisensteinNumerator p x Y = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero hcon
  rw [setIntegral_eisensteinNumerator p hY, hp, mul_zero, zero_add] at hzero
  have hre1 := re_gt_of_xi_shift_eq_zero hp
  have hre2 := re_neg_of_xi_shift_eq_zero hp
  have h1 : (1 : ℂ) + 2 * p ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h2 : (2 : ℂ) * p - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hYC : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have hpow : (Y : ℂ) ^ (1 / 2 - p) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl hYC
  exact (mul_ne_zero (mul_ne_zero (div_ne_zero h1 h2) (xi_two_mul_ne_zero hp)) hpow) hzero

/-! ### The dictionary with the quasinormal spectrum -/

/-- The frequency `ω = i(p - D)` of a mode: after the lift of decay `D`, the field oscillates as
`e^{-iωτ}`. -/
def modeFrequency (D p : ℂ) : ℂ := I * (p - D)

/-- The resonance coordinate of a pole, `ρ = ½ + iz` for `ρ = 1 + 2p`. -/
def poleCoordinate (p : ℂ) : ℂ := (2 * p + 1 / 2) * (-I)

theorem exp_modeFrequency (D p τ : ℂ) :
    Complex.exp (-D * τ) * Complex.exp (p * τ) = Complex.exp (-I * modeFrequency D p * τ) := by
  rw [← Complex.exp_add, modeFrequency]
  congr 1
  linear_combination (-(p - D) * τ) * I_sq

theorem poleCoordinate_zeroCopy (q : XiZeroCopy) :
    poleCoordinate (((q.1 : ℂ) - 1) / 2) = xiSpectralPoint q := by
  rw [poleCoordinate, xiSpectralPoint]
  ring

/-- **The mode frequency is the minus branch of the quasinormal spectrum.** -/
theorem modeFrequency_eq_qnmMinus (n : ℕ) (p : ℂ) :
    modeFrequency (thetaCuspHawkingTopologicalBlackHoleConformalDecay n) p =
      thetaCuspHawkingTopologicalBlackHoleQNMMinus n (poleCoordinate p) := by
  unfold modeFrequency thetaCuspHawkingTopologicalBlackHoleQNMMinus
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum poleCoordinate
  ring

/-- **The plus branch is silent.**  A frequency of the plus branch at a pole is never the frequency of a
mode, because the poles lie in `Re p < 0`. -/
theorem qnmPlus_ne_modeFrequency (n : ℕ) {p p' : ℂ} (hp : xi (1 + 2 * p) = 0)
    (hp' : xi (1 + 2 * p') = 0) :
    thetaCuspHawkingTopologicalBlackHoleQNMPlus n (poleCoordinate p') ≠
      modeFrequency (thetaCuspHawkingTopologicalBlackHoleConformalDecay n) p := by
  intro h
  have heq : p' = -p := by
    unfold thetaCuspHawkingTopologicalBlackHoleQNMPlus modeFrequency
      thetaCuspHawkingTopologicalBlackHoleAngularMomentum poleCoordinate at h
    have hI : I * (p' + p) = 0 := by linear_combination -h
    have := (mul_eq_zero.mp hI).resolve_left I_ne_zero
    linear_combination this
  have h1 := re_neg_of_xi_shift_eq_zero hp
  have h2 := re_neg_of_xi_shift_eq_zero hp'
  rw [heq, Complex.neg_re] at h2
  linarith

/-- The damping rate of a mode is `D - Re p`. -/
theorem modeFrequency_im (D : ℝ) (p : ℂ) : (modeFrequency (D : ℂ) p).im = -(D - p.re) := by
  simp [modeFrequency]

/-- The oscillation of a mode is `-Im p`. -/
theorem modeFrequency_re (D : ℝ) (p : ℂ) : (modeFrequency (D : ℂ) p).re = -p.im := by
  simp [modeFrequency]

/-- At `ρ = β + iγ` a mode of decay `D` rings at rate `D + (1-β)/2`, which is the rate of the causal
symbol. -/
theorem modeRate_zeroCopy (D : ℝ) (q : XiZeroCopy) :
    D - (((q.1 : ℂ) - 1) / 2).re = ringdownRate D (xiSpectralPoint q) := by
  rw [ringdownRate_xiSpectralPoint]
  simp
  ring

/-! ### The fields on the black hole -/

theorem conformalScalar_neumannProfile (ε ξ₀ t r x y : ℝ) :
    conformalScalar (neumannProfile ε ξ₀) t r x y =
      Complex.exp (-(1 / 2 : ℂ) * (hyperboloidalTime t (tortoise r) : ℂ)) / (r : ℂ) *
        wavePacket ε ξ₀ (hyperboloidalTime t (tortoise r)) x y := by
  simp only [conformalScalar, neumannProfile, neumannLift, dampedProfile]
  ring

theorem conformalScalar_dirichletProfile (ε ξ₀ t r x y : ℝ) :
    conformalScalar (dirichletProfile ε ξ₀) t r x y =
      (Real.tanh (tortoise r) : ℂ) *
        Complex.exp (-(3 / 2 : ℂ) * (hyperboloidalTime t (tortoise r) : ℂ)) / (r : ℂ) *
        wavePacket ε ξ₀ (hyperboloidalTime t (tortoise r)) x y := by
  simp only [conformalScalar, dirichletProfile, dirichletLift, dampedProfile]
  ring

/-- **Ringdown of the Neumann field.**  On the exterior `r > 1`, the conformal scalar is the limit over
good heights of the damped modes, up to a remainder that decays faster than every exponential in the
horizon-regular time `τ = t - log(2 cosh x_*)`. -/
theorem neumannField_ringdown {ε : ℝ} (hε : 0 < ε) (ξ₀ x : ℝ) {y : ℝ} (hy : 0 < y) :
    ∃ R : ℝ → ℂ, (∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, ‖R τ‖ ≤ C * Real.exp (-A * τ)) ∧
      ∀ t r : ℝ, Tendsto (fun k =>
          Complex.exp (-(1 / 2 : ℂ) * (hyperboloidalTime t (tortoise r) : ℂ)) / (r : ℂ) *
            ringdownPartialSum ε ξ₀ (hyperboloidalTime t (tortoise r)) x y k) atTop
        (𝓝 (conformalScalar (neumannProfile ε ξ₀) t r x y -
          Complex.exp (-(1 / 2 : ℂ) * (hyperboloidalTime t (tortoise r) : ℂ)) / (r : ℂ) *
            R (hyperboloidalTime t (tortoise r)))) := by
  obtain ⟨R, hR, hlim⟩ := ringdown_expansion hε ξ₀ x hy
  refine ⟨R, hR, fun t r => ?_⟩
  have h := (hlim (hyperboloidalTime t (tortoise r))).const_mul
    (Complex.exp (-(1 / 2 : ℂ) * (hyperboloidalTime t (tortoise r) : ℂ)) / (r : ℂ))
  rw [mul_sub, ← conformalScalar_neumannProfile] at h
  exact h

/-- **Ringdown of the Dirichlet field.** -/
theorem dirichletField_ringdown {ε : ℝ} (hε : 0 < ε) (ξ₀ x : ℝ) {y : ℝ} (hy : 0 < y) :
    ∃ R : ℝ → ℂ, (∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, ‖R τ‖ ≤ C * Real.exp (-A * τ)) ∧
      ∀ t r : ℝ, Tendsto (fun k =>
          (Real.tanh (tortoise r) : ℂ) *
            Complex.exp (-(3 / 2 : ℂ) * (hyperboloidalTime t (tortoise r) : ℂ)) / (r : ℂ) *
            ringdownPartialSum ε ξ₀ (hyperboloidalTime t (tortoise r)) x y k) atTop
        (𝓝 (conformalScalar (dirichletProfile ε ξ₀) t r x y -
          (Real.tanh (tortoise r) : ℂ) *
            Complex.exp (-(3 / 2 : ℂ) * (hyperboloidalTime t (tortoise r) : ℂ)) / (r : ℂ) *
            R (hyperboloidalTime t (tortoise r)))) := by
  obtain ⟨R, hR, hlim⟩ := ringdown_expansion hε ξ₀ x hy
  refine ⟨R, hR, fun t r => ?_⟩
  have h := (hlim (hyperboloidalTime t (tortoise r))).const_mul
    ((Real.tanh (tortoise r) : ℂ) *
      Complex.exp (-(3 / 2 : ℂ) * (hyperboloidalTime t (tortoise r) : ℂ)) / (r : ℂ))
  rw [mul_sub, ← conformalScalar_dirichletProfile] at h
  exact h

end GaloisForLFunctions.BlackHoleRingdown

end
