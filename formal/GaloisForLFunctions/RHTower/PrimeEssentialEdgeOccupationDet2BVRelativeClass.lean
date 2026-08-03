import GaloisForLFunctions.RHTower.PrimeFirstTraceEssentialEdgeSchattenThreshold
import GaloisForLFunctions.HTGeometry.PrimeOccupationPolarizedGammaPhaseSurvival
import GaloisForLFunctions.RHTower.FredholmDeterminantZeta
import GaloisForLFunctions.RHTower.PrimeWoldBVAdjacentDecimation

/-!
# Essential-edge occupation det₂ and the Wold--BV relative class

The strict-preclosure first-trace source has two explicit coordinates whose source-native
contraction cancels the auxiliary Bertrand prime exactly:

`a_p(2) - a_p(1) / farPrime(p) = 1 / p`.

Multiplicative occupation condensation of these recovered nomes gives the reciprocal positive
integer spectrum. Its diagonal kernel is Hilbert--Schmidt, its quadratic Hilbert--Carleman
cocycle is `t² ζ(2) / 2`, and its local det₂ product is the regular Wold--Gamma anomaly
`exp(γt) / Gamma(1-t)`.

Prime decimation is encoded by the single relative spectral-zeta class
`Z_p(s) = (1 - p^(-s)) ζ(s)`. At integral grades `k > 1`, `Z_p(k)` is the actual
trace of the off-multiple Wold defect. At the singular first grade its residue is
`1 - p⁻¹`, exactly the unit-exponential Wold boundary mass and the coefficient of the adjacent
BV continued-source residue.

All results are unconditional. The determinant used here is an exponential and is nowhere zero;
therefore this module constructs the source operator and unifies its regular/singular anomalies,
but does not claim the still-missing arithmetic horizontal annihilation of the Xi landing.
-/

open Filter Topology
open scoped ENNReal NNReal BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions

theorem primeFirstTraceEssentialEdge_apply_one (p : Nat.Primes) :
    primeFirstTraceEssentialSourceDeviation p 1 =
      -(p.1 : ℝ) / ((farPrime p).1 : ℝ) := by
  have hp0 : (p.1 : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hr0 : ((farPrime p).1 : ℝ) ≠ 0 := by
    exact_mod_cast (farPrime p).2.ne_zero
  have hlogp : Real.log (p.1 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast p.2.one_lt))
  rw [primeFirstTraceEssentialSourceDeviation, primeHardyKernelMap_witness]
  simp only [smul_sub, smul_smul]
  simp [primeHardyTail, primeReciprocal, hardyFirstTail_apply_succ,
    lp.single_apply]
  field_simp [hp0, hr0, hlogp]
  ring

def primeFirstTraceEssentialEdgeNomeReal (p : Nat.Primes) : ℝ :=
  primeFirstTraceEssentialSourceDeviation p 2 -
    primeFirstTraceEssentialSourceDeviation p 1 / ((farPrime p).1 : ℝ)

theorem primeFirstTraceEssentialEdgeNomeReal_eq (p : Nat.Primes) :
    primeFirstTraceEssentialEdgeNomeReal p = 1 / (p.1 : ℝ) := by
  have hp0 : (p.1 : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hr0 : ((farPrime p).1 : ℝ) ≠ 0 := by
    exact_mod_cast (farPrime p).2.ne_zero
  rw [primeFirstTraceEssentialEdgeNomeReal,
    primeFirstTraceEssentialSourceDeviation_apply_two,
    primeFirstTraceEssentialEdge_apply_one]
  field_simp [hp0, hr0]
  ring

def primeFirstTraceEssentialEdgeNome (p : Nat.Primes) : ℂ := primeFirstTraceEssentialEdgeNomeReal p

theorem primeFirstTraceEssentialEdgeNome_eq_primeLinearNome (p : Nat.Primes) :
    primeFirstTraceEssentialEdgeNome p = GaloisForLFunctions.primeLinearNome p := by
  rw [primeFirstTraceEssentialEdgeNome, primeFirstTraceEssentialEdgeNomeReal_eq]
  simp [GaloisForLFunctions.primeLinearNome, div_eq_mul_inv]

def primeFirstTraceEssentialEdgeOccupationEntry (ν : Nat.Primes →₀ ℕ) : ℂ :=
  HTGeometry.nomeMonomial primeFirstTraceEssentialEdgeNome ν

theorem primeFirstTraceEssentialEdgeOccupationEntry_eq_standard (ν : Nat.Primes →₀ ℕ) :
    primeFirstTraceEssentialEdgeOccupationEntry ν =
      HTGeometry.nomeMonomial GaloisForLFunctions.primeLinearNome ν := by
  rw [primeFirstTraceEssentialEdgeOccupationEntry]
  congr 1
  exact funext primeFirstTraceEssentialEdgeNome_eq_primeLinearNome

theorem primeFirstTraceEssentialEdgeOccupationEntry_eq (ν : Nat.Primes →₀ ℕ) :
    primeFirstTraceEssentialEdgeOccupationEntry ν =
      (((GaloisForLFunctions.primeProduct ν : ℕ) : ℂ)⁻¹) := by
  rw [primeFirstTraceEssentialEdgeOccupationEntry]
  have hfun : primeFirstTraceEssentialEdgeNome = GaloisForLFunctions.primeLinearNome :=
    funext primeFirstTraceEssentialEdgeNome_eq_primeLinearNome
  rw [hfun, GaloisForLFunctions.nomeMonomial_primeLinearNome]

theorem summable_norm_sq_primeLinearNome :
    Summable (fun p : Nat.Primes =>
      ‖GaloisForLFunctions.primeLinearNome p‖ ^ 2) := by
  have hprime : Summable (fun p : Nat.Primes => ((p : ℝ) ^ 2)⁻¹) :=
    (Real.summable_nat_pow_inv.mpr (by norm_num)).comp_injective
      Subtype.val_injective
  simpa [GaloisForLFunctions.primeLinearNome, norm_inv,
    Complex.norm_natCast, inv_pow] using hprime

theorem summable_norm_sq_primeFirstTraceEssentialEdgeOccupationEntry :
    Summable (fun ν : Nat.Primes →₀ ℕ =>
      ‖primeFirstTraceEssentialEdgeOccupationEntry ν‖ ^ 2) := by
  rw [show primeFirstTraceEssentialEdgeOccupationEntry =
      HTGeometry.nomeMonomial GaloisForLFunctions.primeLinearNome by
    funext ν
    rw [primeFirstTraceEssentialEdgeOccupationEntry]
    congr 1
    exact funext primeFirstTraceEssentialEdgeNome_eq_primeLinearNome]
  exact (HTGeometry.summable_nomeMonomial_pow_iff 1
    GaloisForLFunctions.primeLinearNome
    GaloisForLFunctions.norm_primeLinearNome_lt_one).2
      summable_norm_sq_primeLinearNome

def primeFirstTraceEssentialEdgeOccupationKernel :
    (Nat.Primes →₀ ℕ) × (Nat.Primes →₀ ℕ) → ℂ :=
  HilbertSchmidt.diagMul primeFirstTraceEssentialEdgeOccupationEntry

theorem primeFirstTraceEssentialEdgeOccupationKernel_isHS :
    HilbertSchmidt.IsHS primeFirstTraceEssentialEdgeOccupationKernel := by
  exact HilbertSchmidt.isHS_diagMul_infinite _
    summable_norm_sq_primeFirstTraceEssentialEdgeOccupationEntry

theorem primeFirstTraceEssentialEdgeOccupationKernel_quadraticTrace :
    HilbertSchmidt.hsTraceDiag
        (HilbertSchmidt.hsPow primeFirstTraceEssentialEdgeOccupationKernel 1) =
      riemannZeta 2 := by
  rw [primeFirstTraceEssentialEdgeOccupationKernel, HilbertSchmidt.hsPow_diagMul,
    HilbertSchmidt.hsTraceDiag_diagMul]
  change (∑' ν : Nat.Primes →₀ ℕ, primeFirstTraceEssentialEdgeOccupationEntry ν ^ 2) = _
  calc
    (∑' ν : Nat.Primes →₀ ℕ, primeFirstTraceEssentialEdgeOccupationEntry ν ^ 2) =
        ∑' n : ℕ+,
          primeFirstTraceEssentialEdgeOccupationEntry
              (GaloisForLFunctions.primeOccupationEquivPNat.symm n) ^ 2 := by
        exact (GaloisForLFunctions.primeOccupationEquivPNat.symm.tsum_eq
          (fun ν : Nat.Primes →₀ ℕ => primeFirstTraceEssentialEdgeOccupationEntry ν ^ 2)).symm
    _ = ∑' n : ℕ+, ((((n : ℕ) : ℂ)⁻¹) ^ 2) := by
      apply tsum_congr
      intro n
      rw [primeFirstTraceEssentialEdgeOccupationEntry_eq]
      have hn :
          GaloisForLFunctions.primeProduct
              (GaloisForLFunctions.primeOccupationEquivPNat.symm n) =
            (n : ℕ) := by
        exact congrArg Subtype.val
          (GaloisForLFunctions.primeOccupationEquivPNat.apply_symm_apply n)
      rw [hn]
    _ = ∑' n : ℕ, ((((n : ℂ) + 1)⁻¹) ^ 2) := by
      rw [tsum_pnat_eq_tsum_succ
        (f := fun n : ℕ => (((n : ℂ)⁻¹) ^ 2))]
      apply tsum_congr
      intro n
      norm_num
    _ = riemannZeta 2 := by
      have hsum : Summable (fun n : ℕ => (((n : ℂ) ^ 2)⁻¹)) := by
        have h := (Complex.summable_one_div_nat_cpow (p := (2 : ℂ))).2 (by
          norm_num)
        simpa [one_div, Complex.cpow_natCast] using h
      have hsplit := hsum.sum_add_tsum_nat_add 1
      have hshift :
          (∑' n : ℕ, ((((n : ℂ) + 1) ^ 2)⁻¹)) =
            ∑' n : ℕ, (((n : ℂ) ^ 2)⁻¹) := by
        simpa [Finset.sum_range_succ] using hsplit
      simp_rw [inv_pow]
      rw [hshift]
      simpa [one_div] using
        (zeta_nat_eq_tsum_of_gt_one (k := 2) (by norm_num)).symm

/-- Quadratic Hilbert--Carleman exponent contributed by the essential-edge occupation operator. -/
def primeFirstTraceEssentialEdgeOccupationQuadraticCocycle (t : ℂ) : ℂ :=
  t ^ 2 / 2 * HilbertSchmidt.hsTraceDiag
    (HilbertSchmidt.hsPow primeFirstTraceEssentialEdgeOccupationKernel 1)

theorem primeFirstTraceEssentialEdgeOccupationQuadraticCocycle_eq_woldGammaAnomaly (t : ℂ) :
    primeFirstTraceEssentialEdgeOccupationQuadraticCocycle t =
      t ^ 2 / 2 * riemannZeta 2 := by
  rw [primeFirstTraceEssentialEdgeOccupationQuadraticCocycle,
    primeFirstTraceEssentialEdgeOccupationKernel_quadraticTrace]

theorem primeFirstTraceEssentialEdgeOccupationFredholmDet_eq_completion
    (r : ℝ)
    (hr : r * HilbertSchmidt.hsNorm primeFirstTraceEssentialEdgeOccupationKernel < 1)
    (t : ℂ) (ht : t ∈ Metric.ball (0 : ℂ) r) :
    HilbertSchmidt.fredholmDet primeFirstTraceEssentialEdgeOccupationKernel t =
      GaloisForLFunctions.primeLinearCompletion t := by
  rw [primeFirstTraceEssentialEdgeOccupationKernel,
    HilbertSchmidt.fredholmDet_tprod_diagMul
      primeFirstTraceEssentialEdgeOccupationEntry summable_norm_sq_primeFirstTraceEssentialEdgeOccupationEntry r hr t ht]
  rw [GaloisForLFunctions.primeLinearCompletion,
    HTGeometry.infiniteMultipleEllipticGamma,
    HTGeometry.canonicalWeightProduct]
  apply tprod_congr
  intro ν
  rw [GaloisForLFunctions.primaryFactor_one_genus]
  rw [primeFirstTraceEssentialEdgeOccupationEntry_eq_standard]

theorem primeFirstTraceEssentialEdgeOccupationFredholmDet_eq_gamma
    (r : ℝ)
    (hr : r * HilbertSchmidt.hsNorm primeFirstTraceEssentialEdgeOccupationKernel < 1)
    (t : ℂ) (ht : t ∈ Metric.ball (0 : ℂ) r) :
    HilbertSchmidt.fredholmDet primeFirstTraceEssentialEdgeOccupationKernel t =
      Complex.exp ((Real.eulerMascheroniConstant : ℂ) * t) *
        (Complex.Gamma (1 - t))⁻¹ := by
  rw [primeFirstTraceEssentialEdgeOccupationFredholmDet_eq_completion r hr t ht,
    GaloisForLFunctions.primeLinearCompletion_eq_gamma]

theorem primeFirstTraceEssentialEdgeOccupationFredholmDet_ne_zero (t : ℂ) :
    HilbertSchmidt.fredholmDet primeFirstTraceEssentialEdgeOccupationKernel t ≠ 0 :=
  HilbertSchmidt.fredholmDet_ne_zero _ _

def primeFirstTraceEssentialEdgeOccupationPolarizedDet (t : ℂ) : ℂ :=
  HilbertSchmidt.fredholmDet primeFirstTraceEssentialEdgeOccupationKernel t /
    HilbertSchmidt.fredholmDet primeFirstTraceEssentialEdgeOccupationKernel (-t)

theorem primeFirstTraceEssentialEdgeOccupationPolarizedDet_eq_gammaPhase
    (r : ℝ)
    (hr : r * HilbertSchmidt.hsNorm primeFirstTraceEssentialEdgeOccupationKernel < 1)
    (t : ℂ) (ht : t ∈ Metric.ball (0 : ℂ) r) :
    primeFirstTraceEssentialEdgeOccupationPolarizedDet t =
      Complex.exp
          (2 * (Real.eulerMascheroniConstant : ℂ) * t) *
        (Complex.Gamma (1 + t) / Complex.Gamma (1 - t)) := by
  have hneg : -t ∈ Metric.ball (0 : ℂ) r := by
    simpa [Metric.mem_ball, dist_zero_right] using ht
  rw [primeFirstTraceEssentialEdgeOccupationPolarizedDet,
    primeFirstTraceEssentialEdgeOccupationFredholmDet_eq_completion r hr t ht,
    primeFirstTraceEssentialEdgeOccupationFredholmDet_eq_completion r hr (-t) hneg]
  exact GaloisForLFunctions.primeOccupationPolarizedPhase_eq_gammaRatio t

def primeWoldBVRelativeMomentSummand
    (p : Nat.Primes) (k n : ℕ) : ℂ :=
  Set.indicator {n : ℕ | ¬ p.1 ∣ n}
    (fun n : ℕ => ((n : ℂ) ^ k)⁻¹) n

theorem tsum_primeWoldBVRelativeMomentSummand
    (p : Nat.Primes) {k : ℕ} (hk : 1 < k) :
    ∑' n : ℕ, primeWoldBVRelativeMomentSummand p k n =
      (1 - (((p.1 : ℕ) : ℂ) ^ k)⁻¹) *
        riemannZeta (k : ℂ) := by
  let f : ℕ → ℂ := fun n => ((n : ℂ) ^ k)⁻¹
  let g : ℕ → ℕ := fun n => p.1 * n
  let d : ℕ → ℂ := Set.indicator (Set.range g) f
  have hsumf : Summable f := by
    have h := (Complex.summable_one_div_nat_cpow (p := (k : ℂ))).2 (by
      simpa using hk)
    simpa [f, one_div, Complex.cpow_natCast] using h
  have hgf : ∀ n : ℕ,
      f (g n) = (((p.1 : ℕ) : ℂ) ^ k)⁻¹ * f n := by
    intro n
    simp only [f, g, Nat.cast_mul, mul_pow]
    rw [mul_inv_rev]
    ring
  have hsumfg : Summable (fun n => f (g n)) := by
    exact (hsumf.mul_left ((((p.1 : ℕ) : ℂ) ^ k)⁻¹)).congr
      (fun n => (hgf n).symm)
  have hinj : Function.Injective g := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left p.2.pos hab
  have hsupp : Function.support d ⊆ Set.range g := by
    intro n hn
    by_contra hnot
    apply hn
    change Set.indicator (Set.range g) f n = 0
    exact Set.indicator_of_notMem hnot f
  have hdg : ∀ n : ℕ, d (g n) = f (g n) := by
    intro n
    change Set.indicator (Set.range g) f (g n) = f (g n)
    exact Set.indicator_of_mem
      (show g n ∈ Set.range g from ⟨n, rfl⟩) f
  have hsumd : Summable d := by
    apply (hinj.summable_iff (f := d) ?_).mp
    · exact hsumfg.congr (fun n => (hdg n).symm)
    · intro n hn
      change Set.indicator (Set.range g) f n = 0
      exact Set.indicator_of_notMem hn f
  have htsumd : ∑' n : ℕ, d n =
      (((p.1 : ℕ) : ℂ) ^ k)⁻¹ * riemannZeta (k : ℂ) := by
    have hre := Function.Injective.tsum_eq hinj hsupp
    rw [← hre]
    calc
      ∑' n : ℕ, d (g n) = ∑' n : ℕ, f (g n) := by
        apply tsum_congr hdg
      _ = ∑' n : ℕ,
          (((p.1 : ℕ) : ℂ) ^ k)⁻¹ * f n := by
        apply tsum_congr hgf
      _ = (((p.1 : ℕ) : ℂ) ^ k)⁻¹ * ∑' n : ℕ, f n :=
        tsum_mul_left
      _ = (((p.1 : ℕ) : ℂ) ^ k)⁻¹ * riemannZeta (k : ℂ) := by
        rw [show (∑' n : ℕ, f n) = riemannZeta (k : ℂ) by
          symm
          simpa [f, one_div] using zeta_nat_eq_tsum_of_gt_one hk]
  have hoff : (fun n => primeWoldBVRelativeMomentSummand p k n) =
      fun n => f n - d n := by
    funext n
    by_cases hdiv : p.1 ∣ n
    · obtain ⟨m, hm⟩ := hdiv
      have hdiv' : p.1 ∣ n := ⟨m, hm⟩
      have hmem : n ∈ Set.range g :=
        ⟨m, by simpa [g] using hm.symm⟩
      change Set.indicator {j : ℕ | ¬p.1 ∣ j} f n =
        f n - Set.indicator (Set.range g) f n
      rw [Set.indicator_of_notMem (by simpa using hdiv') f,
        Set.indicator_of_mem hmem f]
      simp
    · have hnotmem : n ∉ Set.range g := by
        rintro ⟨m, hm⟩
        apply hdiv
        exact ⟨m, by simpa [g] using hm.symm⟩
      change Set.indicator {j : ℕ | ¬p.1 ∣ j} f n =
        f n - Set.indicator (Set.range g) f n
      rw [Set.indicator_of_mem (by simpa using hdiv) f,
        Set.indicator_of_notMem hnotmem f]
      simp
  rw [hoff, hsumf.tsum_sub hsumd, htsumd]
  rw [show (∑' n : ℕ, f n) = riemannZeta (k : ℂ) by
    symm
    simpa [f, one_div] using zeta_nat_eq_tsum_of_gt_one hk]
  ring

theorem summable_primeWoldBVRelativeMomentSummand
    (p : Nat.Primes) {k : ℕ} (hk : 1 < k) :
    Summable (primeWoldBVRelativeMomentSummand p k) := by
  have h := (Complex.summable_one_div_nat_cpow (p := (k : ℂ))).2 (by
    simpa using hk)
  have hpow : Summable (fun n : ℕ => ((n : ℂ) ^ k)⁻¹) := by
    simpa [one_div, Complex.cpow_natCast] using h
  exact hpow.indicator {n : ℕ | ¬ p.1 ∣ n}

def primeWoldBVRelativeDefectEntry (p : Nat.Primes) (n : ℕ) : ℂ :=
  primeWoldBVRelativeMomentSummand p 1 n

theorem summable_norm_sq_primeWoldBVRelativeDefectEntry (p : Nat.Primes) :
    Summable (fun n : ℕ => ‖primeWoldBVRelativeDefectEntry p n‖ ^ 2) := by
  have h := (summable_primeWoldBVRelativeMomentSummand p (k := 2) (by omega)).norm
  apply h.congr
  intro n
  by_cases hn : p.1 ∣ n
  · simp [primeWoldBVRelativeDefectEntry, primeWoldBVRelativeMomentSummand, hn]
  · simp [primeWoldBVRelativeDefectEntry, primeWoldBVRelativeMomentSummand, hn,
      norm_inv, norm_pow]

def primeWoldBVRelativeDefectKernel (p : Nat.Primes) : ℕ × ℕ → ℂ :=
  HilbertSchmidt.diagMul (primeWoldBVRelativeDefectEntry p)

theorem primeWoldBVRelativeDefectKernel_isHS (p : Nat.Primes) :
    HilbertSchmidt.IsHS (primeWoldBVRelativeDefectKernel p) := by
  exact HilbertSchmidt.isHS_diagMul_infinite _
    (summable_norm_sq_primeWoldBVRelativeDefectEntry p)

def primeWoldBVRelativeSpectralZeta (p : Nat.Primes) (s : ℂ) : ℂ :=
  (1 - (((p.1 : ℕ) : ℂ) ^ (-s))) * riemannZeta s

theorem primeWoldBVRelativeSpectralZeta_nat_eq_moment
    (p : Nat.Primes) {k : ℕ} (hk : 1 < k) :
    primeWoldBVRelativeSpectralZeta p k =
      ∑' n : ℕ, primeWoldBVRelativeMomentSummand p k n := by
  rw [tsum_primeWoldBVRelativeMomentSummand p hk]
  rw [primeWoldBVRelativeSpectralZeta]
  simp only [Complex.cpow_neg, Complex.cpow_natCast]

theorem primeWoldBVRelativeDefectKernel_quadraticTrace
    (p : Nat.Primes) :
    HilbertSchmidt.hsTraceDiag
        (HilbertSchmidt.hsPow (primeWoldBVRelativeDefectKernel p) 1) =
      primeWoldBVRelativeSpectralZeta p 2 := by
  rw [primeWoldBVRelativeDefectKernel, HilbertSchmidt.hsPow_diagMul,
    HilbertSchmidt.hsTraceDiag_diagMul]
  change (∑' n : ℕ, primeWoldBVRelativeDefectEntry p n ^ 2) =
    primeWoldBVRelativeSpectralZeta p ((2 : ℕ) : ℂ)
  rw [primeWoldBVRelativeSpectralZeta_nat_eq_moment p (k := 2) (by omega)]
  apply tsum_congr
  intro n
  by_cases hn : p.1 ∣ n
  · simp [primeWoldBVRelativeDefectEntry, primeWoldBVRelativeMomentSummand, hn]
  · simp [primeWoldBVRelativeDefectEntry, primeWoldBVRelativeMomentSummand, hn]

theorem primeWoldBVRelativeSpectralZeta_residue_one (p : Nat.Primes) :
    Tendsto
      (fun s : ℂ => (s - 1) * primeWoldBVRelativeSpectralZeta p s)
      (𝓝[≠] (1 : ℂ))
      (𝓝 (1 - (((p.1 : ℕ) : ℂ)⁻¹))) := by
  let P : ℂ := (p.1 : ℕ)
  have hP0 : P ≠ 0 := by
    change ((p.1 : ℕ) : ℂ) ≠ 0
    exact_mod_cast p.2.ne_zero
  letI : NeZero P := ⟨hP0⟩
  have hchar : Tendsto (fun s : ℂ => 1 - P ^ (-s))
      (𝓝[≠] (1 : ℂ)) (𝓝 (1 - P⁻¹)) := by
    have hc : Continuous (fun s : ℂ => 1 - P ^ (-s)) :=
      continuous_const.sub ((continuous_const_cpow P).comp continuous_neg)
    have ht0 : Tendsto (fun s : ℂ => 1 - P ^ (-s))
        (𝓝 (1 : ℂ)) (𝓝 (1 - P ^ (-(1 : ℂ)))) :=
      hc.continuousAt.tendsto
    have ht : Tendsto (fun s : ℂ => 1 - P ^ (-s))
        (𝓝[≠] (1 : ℂ)) (𝓝 (1 - P ^ (-(1 : ℂ)))) :=
      ht0.mono_left inf_le_left
    have hvalue : 1 - P ^ (-(1 : ℂ)) = 1 - P⁻¹ := by
      rw [Complex.cpow_neg, Complex.cpow_one]
    rw [hvalue] at ht
    exact ht
  have hmul := hchar.mul riemannZeta_residue_one
  convert hmul using 1
  · funext s
    rw [primeWoldBVRelativeSpectralZeta]
    change (s - 1) * ((1 - P ^ (-s)) * riemannZeta s) =
      (1 - P ^ (-s)) * ((s - 1) * riemannZeta s)
    ring
  · simp [P]

theorem primeWoldBVRelativeSpectralZeta_residue_one_eq_woldBoundaryMass
    (p : Nat.Primes) :
    Tendsto
      (fun s : ℂ => (s - 1) * primeWoldBVRelativeSpectralZeta p s)
      (𝓝[≠] (1 : ℂ))
      (𝓝 ((unitExponentialWoldBoundaryMass
        (Real.log p.1) : ℝ) : ℂ)) := by
  have hmass :=
    CompactBVPrimeWindow.unitExponentialWoldBoundaryMass_log_nat_cast
      p.1 p.2.pos
  rw [hmass]
  exact primeWoldBVRelativeSpectralZeta_residue_one p

/-- The singular first trace of the same relative spectral-zeta class is the adjacent BV residue.
The statement keeps the continued source residue visible: the singular coefficient is the Wold
boundary mass, whereas the regular quadratic value is `primeWoldSpectralZeta p 2`. -/
theorem primeWoldBVRelativeSpectralZeta_singularBVFirstTrace
    (W : CompactBVPrimeWindow) (p : Nat.Primes) (rho : ℂ) :
    CompactBVPrimeWindow.adjacentOffMultipleResidueValue
        W p.1 p.2.pos rho =
      (1 - (((p.1 : ℕ) : ℂ)⁻¹)) *
        W.continuedSourceResidueValue rho := by
  exact CompactBVPrimeWindow.adjacentOffMultipleResidueValue_eq
    W p.1 p.2.pos rho

theorem primeWoldBVRelative_regularSingularClass
    (W : CompactBVPrimeWindow) (p : Nat.Primes) (rho : ℂ) :
    HilbertSchmidt.hsTraceDiag
        (HilbertSchmidt.hsPow (primeWoldBVRelativeDefectKernel p) 1) =
        primeWoldBVRelativeSpectralZeta p 2 ∧
      Tendsto
        (fun s : ℂ => (s - 1) * primeWoldBVRelativeSpectralZeta p s)
        (𝓝[≠] (1 : ℂ))
        (𝓝 ((unitExponentialWoldBoundaryMass
          (Real.log p.1) : ℝ) : ℂ)) ∧
      CompactBVPrimeWindow.adjacentOffMultipleResidueValue
          W p.1 p.2.pos rho =
        (unitExponentialWoldBoundaryMass
          (Real.log p.1) : ℂ) *
          W.continuedSourceResidueValue rho := by
  exact ⟨primeWoldBVRelativeDefectKernel_quadraticTrace p,
    primeWoldBVRelativeSpectralZeta_residue_one_eq_woldBoundaryMass p,
    CompactBVPrimeWindow.adjacentOffMultipleResidueValue_eq_woldBoundaryMass
      W p.1 p.2.pos rho⟩

end


end RHTower

