import GaloisForLFunctions.HTGeometry.SpectralHardyTraceFormation
import GaloisForLFunctions.HTGeometry.CyclicHeatOrbitFormationCapital
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence
import GaloisForLFunctions.RHTower.EMAnnulusSupply

/-!
# Hardy-trace formation on the Euler shell

On the Euler shell `ℓ²(A_m)`, `λ_n = log n`, `v_n = n^{-σ/2}/√S_m(σ)`:

* `log A_m` violates the half-plane Blaschke condition, since it contains `log(2^m p)` for every odd
  prime `p` and `Σ_p 1/(log p + 1) = ∞` (**(HTF.15)–(HTF.17)**); the spectrum is therefore an `H²`
  uniqueness set;
* exact-time packets `e^{-aL}v` have infinite capital, while the width-`T` averages
  `T^{-1} ∫_a^{a+T} e^{-tL}v dt` cost exactly `1/T` (**(HTF.18)–(HTF.22)**);
* for `σ > 3` the strip packets `x_ρ(n) = v_n (n^{2(Re ρ - 1/2)} - 1)` lie in `ℓ²` for every `ρ` in the
  critical strip, and `q_G(x_ρ) < ∞ ⟺ Re ρ = 1/2` (**(HTF.26)–(HTF.28)**);
* positive aggregation, injective recovery and functional-equation transport preserve this
  selection (**(HTF.29)–(HTF.31)**), and admission of every `ξ`-zero packet is equivalent to the
  Riemann hypothesis (**(HTF.32)**).
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

local notation "ℓ²A" m => lp (fun _ : EulerShell m => ℂ) 2

/-! ## Euler-shell uniqueness -/

/-- **(HTF.16)–(HTF.17)** The Euler-shell spectrum violates the half-plane Blaschke condition:
`Σ_{n ∈ A_m} log n/(1 + log² n) = ∞`.  The odd primes inject by `p ↦ 2^m p`, and
`log n/(1 + log² n) ≥ (2(m+1))^{-1} (log p + 1)^{-1}` there. -/
theorem not_summable_eulerShell_blaschke {m : ℕ} (hm : 1 ≤ m) :
    ¬ Summable fun n : EulerShell m => Real.log (n : ℕ) / (1 + Real.log (n : ℕ) ^ 2) := by
  intro hs
  set ψ : {p : Nat.Primes | (p : ℕ) ≠ 2} → EulerShell m :=
    fun p => ⟨2 ^ m * (p.1 : ℕ), two_pow_mul_prime_mem hm p.1.2 p.2⟩ with hψdef
  have hψ : Function.Injective ψ := fun p q h => by
    have h1 : 2 ^ m * (p.1 : ℕ) = 2 ^ m * (q.1 : ℕ) := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext (Nat.eq_of_mul_eq_mul_left (by positivity) h1))
  have hcomp := (hs.comp_injective hψ).mul_left (2 * ((m : ℝ) + 1))
  have hlow : Summable fun p : {p : Nat.Primes | (p : ℕ) ≠ 2} =>
      (1 / ((Real.log ((p.1 : ℕ) : ℝ) - 0) ^ 1 + 1) : ℝ) := by
    refine hcomp.of_nonneg_of_le (fun p => ?_) fun p => ?_
    · have := Real.log_nonneg (show (1 : ℝ) ≤ ((p.1 : ℕ) : ℝ) by exact_mod_cast p.1.2.one_lt.le)
      rw [sub_zero, pow_one]
      positivity
    · set ℓ := Real.log ((p.1 : ℕ) : ℝ) with hℓ
      have hp2 : (2 : ℝ) ≤ ((p.1 : ℕ) : ℝ) := by exact_mod_cast p.1.2.two_le
      have hp3 : (3 : ℝ) ≤ ((p.1 : ℕ) : ℝ) := by
        have h3 : 3 ≤ (p.1 : ℕ) := by
          have := p.1.2.two_le
          have h2 : (p.1 : ℕ) ≠ 2 := p.2
          omega
        exact_mod_cast h3
      have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by linarith)
      set L := Real.log (((ψ p : EulerShell m) : ℕ) : ℝ) with hL
      have hLeq : L = m * Real.log 2 + ℓ := by
        rw [hL, hψdef]
        push_cast
        rw [Real.log_mul (by positivity) (by linarith), Real.log_pow]
      have hlog2 : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9
        linarith
      have hlog2' : 0 < Real.log 2 := Real.log_pos one_lt_two
      have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hL1 : 1 ≤ L := by
        have h6 : Real.exp 1 ≤ (2 : ℝ) ^ m * ((p.1 : ℕ) : ℝ) := by
          have he := Real.exp_one_lt_d9
          have h2m : (2 : ℝ) ≤ (2 : ℝ) ^ m := by
            calc (2 : ℝ) = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
          nlinarith
        have := Real.log_le_log (Real.exp_pos 1) h6
        rw [Real.log_exp] at this
        rw [hL, hψdef]
        push_cast
        exact this
      have hLle : L ≤ ((m : ℝ) + 1) * (ℓ + 1) := by
        rw [hLeq]
        nlinarith
      simp only [Function.comp_apply, sub_zero, pow_one]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < ℓ + 1)]
      have hrw : 2 * ((m : ℝ) + 1) * (L / (1 + L ^ 2)) * (ℓ + 1) =
          2 * ((m : ℝ) + 1) * L * (ℓ + 1) / (1 + L ^ 2) := by ring
      rw [hrw, le_div_iff₀ (by positivity), one_mul]
      nlinarith [mul_le_mul_of_nonneg_left hLle (show (0 : ℝ) ≤ 2 * L by linarith)]
  apply prime_shifted_log_power_recip_not_summable 1 0 le_rfl
  rw [← summable_subtype_and_compl (s := {p : Nat.Primes | (p : ℕ) ≠ 2})]
  refine ⟨hlow, ?_⟩
  have hfin : ({p : Nat.Primes | (p : ℕ) ≠ 2}ᶜ).Finite :=
    (Set.finite_singleton (⟨2, Nat.prime_two⟩ : Nat.Primes)).subset fun p hp => by
      have hp' : (p : ℕ) = 2 := by
        by_contra hne
        exact hp hne
      exact Set.mem_singleton_iff.2 (Subtype.ext hp')
  haveI := hfin.to_subtype
  exact Summable.of_finite

variable {m : ℕ} (hm : 1 ≤ m) {σ : ℝ} (hσ : 1 < σ)

/-- **(HTF.12)** The Euler-shell spectrum is an `H²` uniqueness set. -/
theorem eulerShell_isHardyUniquenessSet : (eulerShellSource hm hσ).IsHardyUniquenessSet :=
  (eulerShellSource hm hσ).isHardyUniquenessSet_of_not_summable (not_summable_eulerShell_blaschke hm)

/-! ## Exact-time versus averaged packets -/

/-- `e^{-az}`, `a ≥ 0`, is of bounded type on the right half-plane. -/
theorem isHalfPlaneNevanlinna_exp {a : ℝ} (ha : 0 ≤ a) :
    IsHalfPlaneNevanlinna fun z => Complex.exp (-(a * z)) := by
  refine ⟨fun z => Complex.exp (-(a * z)), fun _ => 1, ?_, differentiableOn_const 1, ⟨1, fun w hw => ?_⟩,
    ⟨1, fun _ _ => by simp⟩, fun _ _ => one_ne_zero, fun _ _ => (div_one _).symm⟩
  · exact (Complex.differentiable_exp.comp ((differentiable_const _).mul differentiable_id).neg).differentiableOn
  · rw [Complex.norm_exp, Real.exp_le_one_iff]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have : (0 : ℝ) ≤ a * w.re := mul_nonneg ha (le_of_lt hw)
    linarith

/-- **(HTF.19)** Exact source time is an infinite-capital boundary: `q_G(e^{-aL}v) = ∞`. -/
theorem orbitCostForm_heatOrbit_eq_top {a : ℝ} (ha : 0 ≤ a) :
    (eulerShellSource hm hσ).orbitCostForm ((eulerShellSource hm hσ).heatOrbit a) = ⊤ := by
  rw [HeatSource.heatOrbit_eq_spectralPacket _ ha]
  exact (eulerShellSource hm hσ).orbitCostForm_spectralPacket_eq_top_of_nevanlinna
    (not_summable_eulerShell_blaschke hm) (isHalfPlaneNevanlinna_exp ha)
    (fun ⟨M, h⟩ => not_isHalfPlaneHardy_exp a M h) _

/-- **(HTF.22)** The width-`T` average costs exactly `1/T`, wherever the window sits. -/
theorem orbitCostForm_offsetWindowPacket_eq {a T : ℝ} (ha : 0 ≤ a) (hT : 0 < T) :
    (eulerShellSource hm hσ).orbitCostForm ((eulerShellSource hm hσ).offsetWindowPacket a T) =
      ENNReal.ofReal (1 / T) := by
  refine le_antisymm ?_ ?_
  · rw [HeatSource.offsetWindowPacket_eq _ ha hT, ← norm_offsetWindowControl_sq ha hT]
    exact (eulerShellSource hm hσ).orbitCostForm_heatReachability_le _
  · rw [CyclicHeatSource.orbitCostForm_eq_iInf]
    refine le_iInf₂ fun u hu => ?_
    have hu' : u = offsetWindowControl a T := heatReachability_injective hm hσ
      (hu.trans (HeatSource.offsetWindowPacket_eq _ ha hT))
    rw [hu', norm_offsetWindowControl_sq ha hT]

/-! ## The critical-strip radial packets -/

variable (hσ3 : 3 < σ)

include hσ3 in
/-- **(HTF.27)** For `σ > 3` and `0 < Re ρ < 1` the strip packet satisfies **(HTF.3)**:
`|v_n|² |n^{2a_ρ} - 1|² ≤ 4 n^{2-σ}/S_m(σ)`. -/
theorem summable_criticalPacket {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    Summable fun n => ‖(eulerShellSource hm hσ).v n *
      radialMultiplier (ρ.re - 1 / 2) ((eulerShellSource hm hσ).lam n)‖ ^ 2 := by
  have hS := eulerShellSum_pos hm hσ
  refine ((summable_shell m (by linarith : 1 < σ - 2)).mul_left (4 / eulerShellSum m σ)).of_nonneg_of_le
    (fun _ => by positivity) fun n => ?_
  have hn1 : (1 : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ (n : ℕ) by omega)
  have hn0 : (0 : ℝ) < ((n : ℕ) : ℝ) := by linarith
  rw [norm_mul, mul_pow, norm_sq_eulerShellSource_v, eulerShellSource_lam, radialMultiplier_ofReal,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hL : 0 ≤ Real.log ((n : ℕ) : ℝ) := Real.log_nonneg hn1
  have hexp : Real.exp (2 * (ρ.re - 1 / 2) * Real.log ((n : ℕ) : ℝ)) ≤ ((n : ℕ) : ℝ) := by
    calc Real.exp (2 * (ρ.re - 1 / 2) * Real.log ((n : ℕ) : ℝ))
        ≤ Real.exp (Real.log ((n : ℕ) : ℝ)) := Real.exp_le_exp.2 (by nlinarith)
      _ = ((n : ℕ) : ℝ) := Real.exp_log hn0
  have hsq : (Real.exp (2 * (ρ.re - 1 / 2) * Real.log ((n : ℕ) : ℝ)) - 1) ^ 2 ≤ 4 * ((n : ℕ) : ℝ) ^ 2 := by
    have he0 := Real.exp_pos (2 * (ρ.re - 1 / 2) * Real.log ((n : ℕ) : ℝ))
    nlinarith
  have hpow : ((n : ℕ) : ℝ) ^ (-(σ - 2)) = ((n : ℕ) : ℝ) ^ (-σ) * ((n : ℕ) : ℝ) ^ 2 := by
    rw [show -(σ - 2) = -σ + (2 : ℕ) by push_cast; ring, Real.rpow_add hn0, Real.rpow_natCast]
  rw [hpow]
  calc ((n : ℕ) : ℝ) ^ (-σ) / eulerShellSum m σ *
        (Real.exp (2 * (ρ.re - 1 / 2) * Real.log ((n : ℕ) : ℝ)) - 1) ^ 2
      ≤ ((n : ℕ) : ℝ) ^ (-σ) / eulerShellSum m σ * (4 * ((n : ℕ) : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 4 / eulerShellSum m σ * (((n : ℕ) : ℝ) ^ (-σ) * ((n : ℕ) : ℝ) ^ 2) := by ring

/-- **(HTF.27)** The strip packet `x_ρ = d_{a_ρ}(L)v`, `a_ρ = Re ρ - 1/2` **(HTF.26)**. -/
def criticalPacket {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : ℓ²A m :=
  (eulerShellSource hm hσ).spectralPacket (radialMultiplier (ρ.re - 1 / 2))
    (summable_criticalPacket hm hσ hσ3 h0 h1)

/-- **(HTF.27)** `x_ρ(n) = n^{-σ/2} S_m(σ)^{-1/2} (n^{2a_ρ} - 1)`. -/
theorem criticalPacket_apply {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (n : EulerShell m) :
    criticalPacket hm hσ hσ3 h0 h1 n =
      ((((n : ℕ) : ℝ) ^ (-σ / 2) / Real.sqrt (eulerShellSum m σ) *
        (((n : ℕ) : ℝ) ^ (2 * (ρ.re - 1 / 2)) - 1) : ℝ) : ℂ) := by
  have hn0 : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast (show 0 < (n : ℕ) by omega)
  rw [criticalPacket, HeatSource.spectralPacket_apply, eulerShellSource_v, eulerShellSource_lam,
    radialMultiplier_ofReal, Real.rpow_def_of_pos hn0 (2 * (ρ.re - 1 / 2)),
    mul_comm (Real.log ((n : ℕ) : ℝ)) (2 * (ρ.re - 1 / 2)), ← Complex.ofReal_mul]

/-- **(HTF.28) One fixed Euler shell covers the critical strip.**  For `σ > 3`,
`q_G(x_ρ) < ∞ ⟺ Re ρ = 1/2`. -/
theorem orbitCostForm_criticalPacket_lt_top_iff {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    (eulerShellSource hm hσ).orbitCostForm (criticalPacket hm hσ hσ3 h0 h1) < ⊤ ↔ ρ.re = 1 / 2 := by
  haveI := infinite_eulerShell hm
  rw [criticalPacket, CyclicHeatSource.orbitCostForm_radialPacket_lt_top_iff, sub_eq_zero]

theorem criticalPacket_eq_zero_iff {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    criticalPacket hm hσ hσ3 h0 h1 = 0 ↔ ρ.re = 1 / 2 := by
  refine ⟨fun h => (orbitCostForm_criticalPacket_lt_top_iff hm hσ hσ3 h0 h1).1 ?_, fun h => ?_⟩
  · rw [h, CyclicHeatSource.orbitCostForm_zero]
    exact ENNReal.zero_lt_top
  · exact HeatSource.spectralPacket_radialMultiplier_eq_zero _ (sub_eq_zero.2 h) _

theorem orbitCostForm_criticalPacket_eq_top_iff {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    (eulerShellSource hm hσ).orbitCostForm (criticalPacket hm hσ hσ3 h0 h1) = ⊤ ↔ ρ.re ≠ 1 / 2 := by
  rw [Ne, ← orbitCostForm_criticalPacket_lt_top_iff hm hσ hσ3 h0 h1, lt_top_iff_ne_top, not_not]

/-- **(HTF.29)–(HTF.30) Positive aggregation cannot hide an off-neutral component.**  For a
positive combination `T = Σ_r w_r |x_{ρ_r}⟩⟨x_{ρ_r}|`, `w_r > 0`, of strip packets,
`E_G(T) < ∞ ⟺ Re ρ_r = 1/2` for every `r`. -/
theorem orbitDefectCost_criticalAggregate_lt_top_iff {κ : Type*} (ρ : κ → ℂ)
    (h0 : ∀ r, 0 < (ρ r).re) (h1 : ∀ r, (ρ r).re < 1) (w : κ → ℝ) (hw : ∀ r, 0 < w r)
    {T : (ℓ²A m) →L[ℂ] (ℓ²A m)}
    (hT : HasSum (fun r => ((w r : ℝ) : ℂ) • InnerProductSpace.rankOne ℂ
      (criticalPacket hm hσ hσ3 (h0 r) (h1 r)) (criticalPacket hm hσ hσ3 (h0 r) (h1 r))) T) :
    (eulerShellSource hm hσ).orbitDefectCost T < ⊤ ↔ ∀ r, (ρ r).re = 1 / 2 := by
  classical
  have hpos : ∀ r, (InnerProductSpace.rankOne ℂ (criticalPacket hm hσ hσ3 (h0 r) (h1 r))
      (criticalPacket hm hσ hσ3 (h0 r) (h1 r))).IsPositive := fun r =>
    InnerProductSpace.isPositive_rankOne_self _
  constructor
  · intro hlt r
    by_contra hr
    have htop := (eulerShellSource hm hσ).orbitDefectCost_tsum_eq_top _ hpos w (fun r => (hw r).le) hT
      (hw r) (by rw [CyclicHeatSource.orbitDefectCost_rankOne,
        orbitCostForm_criticalPacket_eq_top_iff]; exact hr)
    exact (lt_top_iff_ne_top.1 hlt) htop
  · intro hall
    rw [(eulerShellSource hm hσ).orbitDefectCost_tsum _ hpos w (fun r => (hw r).le) hT]
    have hzero : ∀ r, (eulerShellSource hm hσ).orbitDefectCost (InnerProductSpace.rankOne ℂ
        (criticalPacket hm hσ hσ3 (h0 r) (h1 r)) (criticalPacket hm hσ hσ3 (h0 r) (h1 r))) = 0 :=
      fun r => by
        rw [(criticalPacket_eq_zero_iff hm hσ hσ3 (h0 r) (h1 r)).2 (hall r), map_zero]
        simp [CyclicHeatSource.orbitDefectCost]
    simp [hzero]

/-! ## Recovery neutrality and the exact boundary -/

/-- The capital of a vector as a formation: `𝔠_W(x) = q_G(x)` for the rank-one source `c ↦ c x`. -/
theorem formationCapital_toSpanSingleton {ι : Type*} [DecidableEq ι] (c : CyclicHeatSource ι)
    (x : lp (fun _ : ι => ℂ) 2) :
    formationCapital c.heatReachability (ContinuousLinearMap.toSpanSingleton ℂ x) = c.orbitCostForm x := by
  rw [← c.orbitDefectCost_eq_formationCapital, ContinuousLinearMap.adjoint_toSpanSingleton,
    ← c.orbitDefectCost_rankOne]
  congr 1

/-- **(HTF.31) Recovery and functional-equation neutrality.**  For every injective transport `R`
(an invertible functional-equation map followed by a common split recovery embedding),
`𝔠_{RW}(R x_ρ) = q_G(x_ρ)`, which is finite exactly on the critical line. -/
theorem formationCapital_comp_criticalPacket {H' : Type*} [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] [CompleteSpace H'] {R : (ℓ²A m) →L[ℂ] H'} (hR : Function.Injective R)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    formationCapital (R ∘L (eulerShellSource hm hσ).heatReachability)
        (R ∘L ContinuousLinearMap.toSpanSingleton ℂ (criticalPacket hm hσ hσ3 h0 h1)) =
      (eulerShellSource hm hσ).orbitCostForm (criticalPacket hm hσ hσ3 h0 h1) ∧
    (formationCapital (R ∘L (eulerShellSource hm hσ).heatReachability)
        (R ∘L ContinuousLinearMap.toSpanSingleton ℂ (criticalPacket hm hσ hσ3 h0 h1)) < ⊤ ↔
      ρ.re = 1 / 2) := by
  have h := formationCapital_comp_of_injective (eulerShellSource hm hσ).heatReachability
    (ContinuousLinearMap.toSpanSingleton ℂ (criticalPacket hm hσ hσ3 h0 h1)) hR
  rw [formationCapital_toSpanSingleton] at h
  exact ⟨h, by rw [h, orbitCostForm_criticalPacket_lt_top_iff]⟩

theorem xi_zero_re_mem_Ioo {ρ : ℂ} (hρ : xi ρ = 0) : 0 < ρ.re ∧ ρ.re < 1 :=
  ⟨xi_zero_re_pos hρ, xi_zero_re_lt_one hρ⟩

/-- **(HTF.32) The exact RH boundary.**  Admission of every `ξ`-zero strip packet by the source
formation is equivalent to the Riemann hypothesis; equivalently every such packet vanishes. -/
theorem forall_xi_zero_criticalPacket_admitted_iff_riemannHypothesis :
    ((∀ (ρ : ℂ) (hρ : xi ρ = 0), (eulerShellSource hm hσ).orbitCostForm
        (criticalPacket hm hσ hσ3 (xi_zero_re_mem_Ioo hρ).1 (xi_zero_re_mem_Ioo hρ).2) < ⊤) ↔
      RiemannHypothesis) ∧
    ((∀ (ρ : ℂ) (hρ : xi ρ = 0),
        criticalPacket hm hσ hσ3 (xi_zero_re_mem_Ioo hρ).1 (xi_zero_re_mem_Ioo hρ).2 = 0) ↔
      RiemannHypothesis) := by
  rw [riemannHypothesis_iff_xi_zero_re_eq_half]
  exact ⟨forall_congr' fun ρ => ⟨fun h hρ => (orbitCostForm_criticalPacket_lt_top_iff hm hσ hσ3 _ _).1 (h hρ),
      fun h hρ => (orbitCostForm_criticalPacket_lt_top_iff hm hσ hσ3 _ _).2 (h hρ)⟩,
    forall_congr' fun ρ => ⟨fun h hρ => (criticalPacket_eq_zero_iff hm hσ hσ3 _ _).1 (h hρ),
      fun h hρ => (criticalPacket_eq_zero_iff hm hσ hσ3 _ _).2 (h hρ)⟩⟩

end GaloisForLFunctions.HTGeometry
