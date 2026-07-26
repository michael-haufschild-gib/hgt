import GaloisForLFunctions.RHTower.CompletedFluxCrossOrderReflection
import GaloisForLFunctions.RHTower.CompletedLogDerivStrip

/-!
# Fixed all-order prime--archimedean decomposition of the completed flux germ

At every point of the open critical strip, the removable completed-flux germ is the sum of two
fixed analytic germs: the meromorphically continued von Mangoldt flux and the archimedean/boundary
flux.  The identity is local analytic equality, hence holds coefficientwise at every Taylor order.
No finite prime packet, cutoff, or order-dependent interpolation is introduced.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- A strip-local zeta peel retaining the actual factorization, not just its logarithmic
derivative. -/
theorem exists_riemannZeta_peel_ball_of_mem_strip {ρ : ℂ}
    (hstrip : 0 < ρ.re ∧ ρ.re < 1) :
    ∃ R > 0, ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (ball ρ R) ∧
      (∀ z ∈ ball ρ R, h z ≠ 0) ∧
      ∀ z ∈ ball ρ R,
        riemannZeta z = (z - ρ) ^ (analyticOrderAt xi ρ).toNat * h z := by
  let U : Set ℂ := {z | 0 < z.re ∧ z.re < 1}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hρU : ρ ∈ U := hstrip
  have hzetaU : AnalyticOnNhd ℂ riemannZeta U := by
    exact analyticOn_riemannZeta.mono (by
      intro z hz
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (show z ≠ 1 by
          intro h
          subst z
          exact (lt_irrefl 1 hz.2)))
  have horder := xi_analyticOrderAt_eq_riemannZeta_of_mem_strip hstrip
  have hm : analyticOrderAt riemannZeta ρ =
      ((analyticOrderAt xi ρ).toNat : ℕ∞) := by
    rw [← horder]
    exact (ENat.coe_toNat (xi_order_ne_top ρ)).symm
  obtain ⟨h, hhan, hh0, hfact, _⟩ := exists_peel hUopen hzetaU hρU hm
  have hnonzero : {z : ℂ | h z ≠ 0} ∈ nhds ρ :=
    (hhan ρ hρU).continuousAt.eventually_ne hh0
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hUopen.mem_nhds hρU) hnonzero)
  have hballU : ball ρ R ⊆ U := fun z hz => (hRsub hz).1
  have hhball : ∀ z ∈ ball ρ R, h z ≠ 0 := fun z hz => (hRsub hz).2
  exact ⟨R, hR, h, hhan.mono hballU, hhball,
    fun z hz => hfact z (hballU hz)⟩

/-- The removable germ of the continued infinite von Mangoldt flux. -/
def infinitePrimeFluxGermAt (ρ x : ℂ) : ℂ :=
  if x = 0 then -((analyticOrderAt xi ρ).toNat : ℂ)
  else x * infinitePrimeFlux (ρ + x)

/-- The archimedean plus boundary contribution to the local completed flux. -/
def archimedeanBoundaryFluxGermAt (ρ x : ℂ) : ℂ :=
  x * (-logDeriv archFactor (ρ + x))

@[simp] theorem infinitePrimeFluxGermAt_zero (ρ : ℂ) :
    infinitePrimeFluxGermAt ρ 0 = -((analyticOrderAt xi ρ).toNat : ℂ) := by
  simp [infinitePrimeFluxGermAt]

@[simp] theorem archimedeanBoundaryFluxGermAt_zero (ρ : ℂ) :
    archimedeanBoundaryFluxGermAt ρ 0 = 0 := by
  simp [archimedeanBoundaryFluxGermAt]

/-- Pointwise decomposition of the completed flux away from zeta zeros in the strip. -/
theorem seamFluxCochain_eq_infinitePrimeFlux_add_archimedean {s : ℂ}
    (hstrip : 0 < s.re ∧ s.re < 1) (hz : riemannZeta s ≠ 0) :
    seamFluxCochain s = infinitePrimeFlux s - logDeriv archFactor s := by
  let U : Set ℂ := {z | 0 < z.re ∧ z.re < 1}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hsU : s ∈ U := hstrip
  have hev : xi =ᶠ[nhds s] fun z => archFactor z * riemannZeta z := by
    filter_upwards [hUopen.mem_nhds hsU] with z hzstrip
    exact xi_eq_archFactor_mul_zeta
      (by intro h; subst z; simpa using hzstrip.1)
      (by intro h; subst z; simpa using hzstrip.2)
      (Gammaℝ_ne_zero_of_re_pos hzstrip.1)
  have hlog : logDeriv xi s =
      logDeriv (fun z => archFactor z * riemannZeta z) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [seamFluxCochain, infinitePrimeFlux, hlog,
    logDeriv_completed_split_strip hstrip hz]
  ring

/-- The continued infinite-prime flux has a removable analytic germ at every strip point. -/
theorem infinitePrimeFluxGermAt_analyticAt_zero {ρ : ℂ}
    (hstrip : 0 < ρ.re ∧ ρ.re < 1) :
    AnalyticAt ℂ (infinitePrimeFluxGermAt ρ) 0 := by
  obtain ⟨R, hR, h, hhan, hh0, hlocal⟩ :=
    exists_riemannZeta_normalizedLogDeriv_factorization_of_mem_strip hstrip
  have hρball : ρ ∈ ball ρ R := mem_ball_self hR
  have hha : AnalyticAt ℂ h ρ := hhan ρ hρball
  have hlog : AnalyticAt ℂ (logDeriv h) ρ := by
    rw [show logDeriv h = fun z => deriv h z / h z by
      funext z
      rw [logDeriv_apply]]
    exact hha.deriv.div hha (hh0 ρ hρball)
  have hshift : AnalyticAt ℂ (fun x : ℂ => logDeriv h (ρ + x)) 0 := by
    have hcomp := AnalyticAt.comp_of_eq hlog
      (show AnalyticAt ℂ (fun x : ℂ => ρ + x) 0 by fun_prop) (by simp)
    simpa [Function.comp] using hcomp
  have hmodel : AnalyticAt ℂ
      (fun x : ℂ => -((analyticOrderAt xi ρ).toNat : ℂ) -
        x * logDeriv h (ρ + x)) 0 :=
    analyticAt_const.sub (analyticAt_id.mul hshift)
  apply hmodel.congr
  have hshiftTendsto : Tendsto (fun x : ℂ => ρ + x) (nhds 0) (nhds ρ) := by
    have hc : Continuous (fun x : ℂ => ρ + x) := continuous_const.add continuous_id
    simpa using hc.tendsto 0
  have hball : ∀ᶠ x : ℂ in nhds 0, ρ + x ∈ ball ρ R :=
    hshiftTendsto (isOpen_ball.mem_nhds hρball)
  filter_upwards [hball] with x hxball
  by_cases hx : x = 0
  · subst x
    simp
  · rw [infinitePrimeFluxGermAt, if_neg hx, infinitePrimeFlux]
    have hzne : ρ + x ≠ ρ := by simpa using hx
    have hfactor := hlocal (ρ + x) hxball hzne
    simp only [add_sub_cancel_left] at hfactor
    calc
      -((analyticOrderAt xi ρ).toNat : ℂ) - x * logDeriv h (ρ + x) =
          -(((analyticOrderAt xi ρ).toNat : ℂ) + x * logDeriv h (ρ + x)) := by ring
      _ = -(x * logDeriv riemannZeta (ρ + x)) := by rw [← hfactor]
      _ = x * -logDeriv riemannZeta (ρ + x) := by ring

/-- The Gamma/boundary local flux is analytic at the local origin throughout the strip. -/
theorem archimedeanBoundaryFluxGermAt_analyticAt_zero {ρ : ℂ}
    (hstrip : 0 < ρ.re ∧ ρ.re < 1) :
    AnalyticAt ℂ (archimedeanBoundaryFluxGermAt ρ) 0 := by
  have hpoly : AnalyticAt ℂ (fun z : ℂ => z * (z - 1) / 2) ρ := by fun_prop
  have harch : AnalyticAt ℂ archFactor ρ :=
    hpoly.mul (Gammaℝ_analyticAt (Gammaℝ_ne_zero_of_re_pos hstrip.1))
  have hlog : AnalyticAt ℂ (logDeriv archFactor) ρ := by
    rw [show logDeriv archFactor = fun z => deriv archFactor z / archFactor z by
      funext z
      rw [logDeriv_apply]]
    exact harch.deriv.div harch (archFactor_ne_zero_strip hstrip)
  have hshift : AnalyticAt ℂ (fun x : ℂ => logDeriv archFactor (ρ + x)) 0 := by
    have hcomp := AnalyticAt.comp_of_eq hlog
      (show AnalyticAt ℂ (fun x : ℂ => ρ + x) 0 by fun_prop) (by simp)
    simpa [Function.comp] using hcomp
  exact analyticAt_id.mul hshift.neg

/-- Local analytic-germ identity attaching the completed flux to the actual continued prime source
and the archimedean/boundary source. -/
theorem completedFluxGermAt_eq_prime_add_archimedean_eventually {ρ : ℂ}
    (hstrip : 0 < ρ.re ∧ ρ.re < 1) :
    completedFluxGermAt ρ =ᶠ[nhds 0]
      fun x => infinitePrimeFluxGermAt ρ x + archimedeanBoundaryFluxGermAt ρ x := by
  obtain ⟨R, hR, h, hhan, hh0, hfact⟩ :=
    exists_riemannZeta_peel_ball_of_mem_strip hstrip
  let U : Set ℂ := {z | 0 < z.re ∧ z.re < 1}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hρU : ρ ∈ U := hstrip
  have hshiftTendsto : Tendsto (fun x : ℂ => ρ + x) (nhds 0) (nhds ρ) := by
    have hc : Continuous (fun x : ℂ => ρ + x) := continuous_const.add continuous_id
    simpa using hc.tendsto 0
  have hball : ∀ᶠ x : ℂ in nhds 0, ρ + x ∈ ball ρ R :=
    hshiftTendsto (isOpen_ball.mem_nhds (mem_ball_self hR))
  have hstripEventually : ∀ᶠ x : ℂ in nhds 0, ρ + x ∈ U :=
    hshiftTendsto (hUopen.mem_nhds hρU)
  filter_upwards [hball, hstripEventually] with x hxball hxstrip
  by_cases hx : x = 0
  · subst x
    simp
  · have hpow : x ^ (analyticOrderAt xi ρ).toNat ≠ 0 := pow_ne_zero _ hx
    have hzeta : riemannZeta (ρ + x) ≠ 0 := by
      rw [hfact (ρ + x) hxball]
      exact mul_ne_zero (by simpa using hpow) (hh0 (ρ + x) hxball)
    have hsplit := seamFluxCochain_eq_infinitePrimeFlux_add_archimedean hxstrip hzeta
    rw [completedFluxGermAt, if_neg hx, infinitePrimeFluxGermAt, if_neg hx,
      archimedeanBoundaryFluxGermAt]
    rw [hsplit]
    ring

/-- Taylor coefficients of the removable continued infinite-prime germ. -/
def infinitePrimeFluxTaylorCoeff (ρ : ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n (infinitePrimeFluxGermAt ρ) 0 / n.factorial

/-- Taylor coefficients of the archimedean/boundary germ. -/
def archimedeanBoundaryFluxTaylorCoeff (ρ : ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n (archimedeanBoundaryFluxGermAt ρ) 0 / n.factorial

/-- The completed coefficient sequence is the fixed prime sequence plus the fixed archimedean
sequence at every order. -/
theorem completedFluxTaylorCoeff_eq_prime_add_archimedean {ρ : ℂ}
    (hstrip : 0 < ρ.re ∧ ρ.re < 1) (n : ℕ) :
    completedFluxTaylorCoeff ρ n = infinitePrimeFluxTaylorCoeff ρ n +
      archimedeanBoundaryFluxTaylorCoeff ρ n := by
  have heq := completedFluxGermAt_eq_prime_add_archimedean_eventually hstrip
  have hder := heq.iteratedDeriv_eq n
  have hprime : ContDiffAt ℂ n (infinitePrimeFluxGermAt ρ) 0 :=
    (infinitePrimeFluxGermAt_analyticAt_zero hstrip).contDiffAt
  have harch : ContDiffAt ℂ n (archimedeanBoundaryFluxGermAt ρ) 0 :=
    (archimedeanBoundaryFluxGermAt_analyticAt_zero hstrip).contDiffAt
  rw [show (fun x => infinitePrimeFluxGermAt ρ x +
    archimedeanBoundaryFluxGermAt ρ x) =
      infinitePrimeFluxGermAt ρ + archimedeanBoundaryFluxGermAt ρ by rfl,
    iteratedDeriv_add hprime harch] at hder
  rw [completedFluxTaylorCoeff, infinitePrimeFluxTaylorCoeff,
    archimedeanBoundaryFluxTaylorCoeff, hder]
  ring

/-- **Fixed prime--archimedean FE compatibility.**  The parity defect of the continued prime
coefficient sequence is exactly the opposite parity defect of the archimedean/boundary sequence,
at every order of one fixed pair of germs. -/
theorem infinitePrimeFluxTaylorCoeff_reflection_defect_eq_archimedean {ρ : ℂ}
    (hstrip : 0 < ρ.re ∧ ρ.re < 1) (n : ℕ) :
    (-1 : ℂ) ^ n * infinitePrimeFluxTaylorCoeff (1 - ρ) n -
        infinitePrimeFluxTaylorCoeff ρ n =
      archimedeanBoundaryFluxTaylorCoeff ρ n -
        (-1 : ℂ) ^ n * archimedeanBoundaryFluxTaylorCoeff (1 - ρ) n := by
  have hpairStrip : 0 < (1 - ρ).re ∧ (1 - ρ).re < 1 := by
    change 0 < 1 - ρ.re ∧ 1 - ρ.re < 1
    constructor <;> linarith [hstrip.1, hstrip.2]
  have hρ := completedFluxTaylorCoeff_eq_prime_add_archimedean hstrip n
  have hpair := completedFluxTaylorCoeff_eq_prime_add_archimedean hpairStrip n
  have hreflect := completedFluxTaylorCoeff_reflection ρ n
  rw [hρ, hpair] at hreflect
  linear_combination hreflect

/-- At the FE fixed point, every odd continued-prime coefficient is cancelled exactly by the
corresponding archimedean/boundary coefficient. -/
theorem infinitePrimeFluxTaylorCoeff_central_odd_eq_neg_archimedean
    {n : ℕ} (hn : Odd n) :
    infinitePrimeFluxTaylorCoeff (1 / 2 : ℂ) n =
      -archimedeanBoundaryFluxTaylorCoeff (1 / 2 : ℂ) n := by
  have hstrip : 0 < ((1 / 2 : ℂ).re) ∧ ((1 / 2 : ℂ).re) < 1 := by
    norm_num
  have hdecomp := completedFluxTaylorCoeff_eq_prime_add_archimedean hstrip n
  rw [completedFluxTaylorCoeff_central_odd_eq_zero hn] at hdecomp
  exact eq_neg_of_add_eq_zero_left hdecomp.symm

end

end RHTower

namespace RHTower

noncomputable section

/-- Two analytic one-variable germs with identical iterated derivatives agree locally. -/
theorem analyticAt_eventuallyEq_of_iteratedDeriv_eq {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hder : ∀ n : ℕ, iteratedDeriv n f z = iteratedDeriv n g z) :
    f =ᶠ[𝓝 z] g := by
  have hd : AnalyticAt ℂ (f - g) z := hf.sub hg
  have hzero : ∀ n : ℕ, iteratedDeriv n (f - g) z = 0 := by
    intro n
    rw [iteratedDeriv_sub hf.contDiffAt hg.contDiffAt, hder n, sub_self]
  have htop : analyticOrderAt (f - g) z = ⊤ := by
    by_contra hfin
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
    have hle : ((m + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (f - g) z := by
      rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hd]
      intro i _hi
      exact hzero i
    rw [← hm] at hle
    have : (m + 1 : ℕ) ≤ m := by exact_mod_cast hle
    omega
  have hev : (f - g) =ᶠ[𝓝 z] 0 := analyticOrderAt_eq_top.mp htop
  filter_upwards [hev] with x hx
  exact sub_eq_zero.mp hx

end

end RHTower
