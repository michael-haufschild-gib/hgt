import GaloisForLFunctions.RHTower.FermiNymanLogarithmicWitness
import GaloisForLFunctions.RHTower.FermiNymanWitnessNegativeIndex
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow

/-!
# Literal confluent pairing of Fermi witnesses

For `c(s) = 2^(-s) - 1/2`, differentiate the literal spurious pairing
`q(g_l, t^(conj(s)-1)) = c(s)/(s-d_l)`. Multiplication by the analytic reciprocal of `c`
normalizes the logarithmic jet packet. Every normalized jet below the analytic order of zeta
is a Fermi witness, and its exact pairing is

`q(g_l, h_(rho,j)) = (-1)^j j! ((rho-d_l)^(-1))^(j+1)`.

Thus repeated zeros give genuine confluent Cauchy columns without a simplicity hypothesis.
Compactly supported spurious cuts justify differentiation of both defining integrals.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

def spuriousCut (k : ℤ) (c : ℝ) : ℝ → ℂ :=
  (Ioc (0 : ℝ) c).indicator (spuriousWitness k)

theorem measurable_spuriousCut (k : ℤ) {c : ℝ} (hc : c ≤ 1) : Measurable (spuriousCut k c) := by
  have hcont : ContinuousOn (spuriousWitness k) (Ioc (0 : ℝ) c) :=
    (continuousOn_powerWitness _).mono (Ioc_subset_Ioc_right hc)
  have h := ContinuousOn.measurable_piecewise hcont
    (continuousOn_const (c := (0 : ℂ))) measurableSet_Ioc
  convert h using 1
  funext t
  by_cases ht : t ∈ Ioc (0 : ℝ) c
  · simp [spuriousCut, ht]
  · simp [spuriousCut, ht]

theorem norm_spuriousCut_le_one (k : ℤ) (c t : ℝ) : ‖spuriousCut k c t‖ ≤ 1 := by
  unfold spuriousCut
  by_cases ht : t ∈ Ioc (0 : ℝ) c
  · rw [Set.indicator_of_mem ht]
    simp only [spuriousWitness, powerWitness]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht.1]
    simp [Complex.sub_re, Complex.conj_re, dyadicSpuriousMode_re]
  · rw [Set.indicator_of_notMem ht, norm_zero]
    exact zero_le_one

theorem mellinRapid_spuriousCut (k : ℤ) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    MellinRapid (spuriousCut k c) :=
  mellinRapid_of_bounded_rightSupport (measurable_spuriousCut k hc1)
    (norm_spuriousCut_le_one k c) hc0 (fun t ht => by
      exact Set.indicator_of_notMem (f := spuriousWitness k)
        (fun h : t ∈ Ioc (0 : ℝ) c => not_le_of_gt ht h.2))

theorem mellin_logWeighted_spuriousCut (k : ℤ) (c : ℝ) (j : ℕ) (ρ : ℂ) :
    mellin (logWeighted (spuriousCut k c) j) ρ =
      ∫ t in Ioc (0 : ℝ) c, spuriousWitness k t *
        (starRingEnd ℂ) (logPowerWitness ((starRingEnd ℂ) ρ) j t) := by
  unfold mellin
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self]
  · refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    simp only [logWeighted, spuriousCut, Set.indicator_of_mem ht, logPowerWitness,
      powerWitness, map_mul, map_pow, Complex.conj_ofReal, conj_ofReal_cpow ht.1,
      map_sub, map_one, Complex.conj_conj, Complex.real_smul, smul_eq_mul,
      Complex.ofReal_pow]
    ring
  · intro t ht
    simp [logWeighted, spuriousCut, Set.indicator_of_notMem ht.2]

theorem MellinRapid.analyticAt_mellin {f : ℝ → ℂ} (hf : MellinRapid f) {s : ℂ}
    (hs : 0 < s.re) : AnalyticAt ℂ (mellin f) s := by
  have hd : DifferentiableOn ℂ (mellin f) {z : ℂ | 0 < z.re} := by
    intro z hz
    have h := (hasDerivAt_mellin_logWeighted hf 0 hz).differentiableAt
    rw [show RHTower.logWeighted f 0 = f from funext (logWeighted_zero f)] at h
    exact h.differentiableWithinAt
  exact (hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)) s hs

def dyadicCoupling (z : ℂ) : ℂ := (2 : ℂ) ^ (-z) - 1 / 2
def dyadicCouplingInv (z : ℂ) : ℂ := (dyadicCoupling z)⁻¹

theorem analyticAt_dyadicCoupling (z : ℂ) : AnalyticAt ℂ dyadicCoupling z := by
  have hd : Differentiable ℂ (fun s : ℂ => (2 : ℂ) ^ (-s)) :=
    fun _ => (differentiableAt_id.neg).const_cpow (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
  exact (hd.analyticAt z).sub analyticAt_const

theorem analyticAt_dyadicCouplingInv {z : ℂ} (hz : z.re < 1) :
    AnalyticAt ℂ dyadicCouplingInv z :=
  (analyticAt_dyadicCoupling z).inv (two_cpow_neg_ne_half hz)

theorem dyadicForm_spurious_logPower (l j : ℕ) {ρ : ℂ} (hρ : 0 < ρ.re) :
    dyadicForm (spuriousWitness ((l : ℤ) + 1))
      (logPowerWitness ((starRingEnd ℂ) ρ) j) =
      iteratedDeriv j (fun z => dyadicCoupling z / (z - spuriousNode l)) ρ := by
  let k : ℤ := (l : ℤ) + 1
  let F : ℂ → ℂ := fun z => mellin (spuriousCut k (1 / 2)) z -
    (1 / 2 : ℂ) * mellin (spuriousCut k 1) z
  have hhalf := mellinRapid_spuriousCut k (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hone := mellinRapid_spuriousCut k zero_lt_one le_rfl
  have hHa := hhalf.analyticAt_mellin hρ
  have hOa := hone.analyticAt_mellin hρ
  have hF : ∀ z : ℂ, 0 < z.re → F z = dyadicCoupling z / (z - spuriousNode l) := by
    intro z hz
    change mellin (spuriousCut k (1 / 2)) z -
      (1 / 2 : ℂ) * mellin (spuriousCut k 1) z = _
    rw [← show logWeighted (spuriousCut k (1 / 2)) 0 = spuriousCut k (1 / 2) from
      funext (logWeighted_zero _),
      ← show logWeighted (spuriousCut k 1) 0 = spuriousCut k 1 from funext (logWeighted_zero _),
      mellin_logWeighted_spuriousCut, mellin_logWeighted_spuriousCut]
    simp only [logPowerWitness, pow_zero, one_mul]
    unfold spuriousWitness
    rw [crossTerm_spurious_zeroWitness k hz]
    unfold dyadicCoupling spuriousNode k
    congr 1
    ring
  have hev : F =ᶠ[𝓝 ρ] (fun z => dyadicCoupling z / (z - spuriousNode l)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hρ] with z hz
    exact hF z hz
  rw [← hev.iteratedDeriv_eq j]
  change _ = iteratedDeriv j ((mellin (spuriousCut k (1 / 2))) -
    ((fun _ => (1 / 2 : ℂ)) * mellin (spuriousCut k 1))) ρ
  rw [iteratedDeriv_sub hHa.contDiffAt (analyticAt_const.mul hOa).contDiffAt]
  change _ = iteratedDeriv j (mellin (spuriousCut k (1 / 2))) ρ -
    iteratedDeriv j (fun z => (1 / 2 : ℂ) * mellin (spuriousCut k 1) z) ρ
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_mellin hhalf j hρ,
    iteratedDeriv_mellin hone j hρ, mellin_logWeighted_spuriousCut,
    mellin_logWeighted_spuriousCut]
  rfl

theorem dyadicForm_sum_left {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (c : ι → ℂ) {v : ℝ → ℂ} (hv : IsFermiNymanWitness v)
    (hf : ∀ i ∈ s, IsFermiNymanWitness (f i)) :
    dyadicForm (fun t => ∑ i ∈ s, c i * f i t) v = ∑ i ∈ s, c i * dyadicForm (f i) v := by
  classical
  have hexp : ∀ t, (∑ i ∈ s, c i * f i t) * (starRingEnd ℂ) (v t) =
      ∑ i ∈ s, c i * (f i t * (starRingEnd ℂ) (v t)) := by
    intro t
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hI : ∀ S : Set ℝ, S ⊆ Ioc (0 : ℝ) 1 →
      (∫ t in S, (∑ i ∈ s, c i * f i t) * (starRingEnd ℂ) (v t)) =
        ∑ i ∈ s, c i * ∫ t in S, f i t * (starRingEnd ℂ) (v t) := by
    intro S hS
    simp_rw [hexp]
    rw [integral_finsetSum _ (fun i hi =>
      (((hf i hi).integrableOn_mul_conj_witness hv).mono_set hS).const_mul _)]
    exact Finset.sum_congr rfl (fun _ _ => integral_const_mul _ _)
  unfold dyadicForm
  rw [hI _ (Ioc_subset_Ioc_right (by norm_num)), hI _ subset_rfl,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem dyadicForm_sum_right {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (c : ι → ℂ) {v : ℝ → ℂ} (hv : IsFermiNymanWitness v)
    (hf : ∀ i ∈ s, IsFermiNymanWitness (f i)) :
    dyadicForm v (fun t => ∑ i ∈ s, c i * f i t) =
      ∑ i ∈ s, (starRingEnd ℂ) (c i) * dyadicForm v (f i) := by
  rw [dyadicForm_conj, dyadicForm_sum_left s f c hv hf, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← dyadicForm_conj]

/-- The conjugate parameter jet of `t^(s-1)/c(s)`, expanded into literal log-power witnesses. -/
def normalizedFermiJet (ρ : ℂ) (j : ℕ) (t : ℝ) : ℂ :=
  ∑ r ∈ Finset.range (j + 1),
    (starRingEnd ℂ) ((j.choose r : ℂ) * iteratedDeriv (j - r) dyadicCouplingInv ρ) *
      logPowerWitness ((starRingEnd ℂ) ρ) r t

theorem isFermiNymanWitness_normalizedFermiJet {ρ : ℂ}
    (h1 : 1 / 2 < ρ.re) (h2 : ρ.re < 1) (j : ℕ)
    (hj : ((j + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt riemannZeta ρ) :
    IsFermiNymanWitness (normalizedFermiJet ρ j) := by
  refine isFermiNymanWitness_finsetSum (Finset.range (j + 1))
    (fun r => logPowerWitness ((starRingEnd ℂ) ρ) r)
    (fun r => (starRingEnd ℂ) ((j.choose r : ℂ) *
      iteratedDeriv (j - r) dyadicCouplingInv ρ)) (fun r hr => ?_)
  apply isFermiNymanWitness_logPower_of_order h1 h2 r
  exact le_trans (by exact_mod_cast Nat.add_le_add_right (Nat.le_of_lt_succ (Finset.mem_range.1 hr)) 1) hj

theorem iteratedDeriv_shifted_inv (j : ℕ) (d ρ : ℂ) :
    iteratedDeriv j (fun z : ℂ => (z - d)⁻¹) ρ =
      (-1 : ℂ) ^ j * (j.factorial : ℂ) * ((ρ - d)⁻¹) ^ (j + 1) := by
  have h := iteratedDerivWithin_one_div (𝕜 := ℂ) j isOpen_univ (mem_univ (ρ - d))
  rw [iteratedDerivWithin_univ] at h
  simp only [one_div] at h
  rw [iteratedDeriv_comp_sub_const j (fun z : ℂ => z⁻¹) d]
  change iteratedDeriv j (fun z : ℂ => z⁻¹) (ρ - d) = _
  rw [h]
  congr 1
  rw [show (-1 - (j : ℤ)) = -(↑(j + 1) : ℤ) from by omega,
    zpow_neg, zpow_natCast, inv_pow]

/-- Normalization removes the source unit and exposes the exact confluent Cauchy column. -/
theorem dyadicForm_spurious_normalizedFermiJet (l j : ℕ) {ρ : ℂ}
    (h1 : 1 / 2 < ρ.re) (h2 : ρ.re < 1)
    (hj : ((j + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt riemannZeta ρ) :
    dyadicForm (spuriousWitness ((l : ℤ) + 1)) (normalizedFermiJet ρ j) =
      (-1 : ℂ) ^ j * (j.factorial : ℂ) * ((ρ - spuriousNode l)⁻¹) ^ (j + 1) := by
  have hp : 0 < ρ.re := by linarith
  have hden : ρ - spuriousNode l ≠ 0 := by
    intro h
    have h' := congrArg Complex.re (sub_eq_zero.1 h)
    rw [spuriousNode_re] at h'
    linarith
  have hq : AnalyticAt ℂ (fun z => dyadicCoupling z / (z - spuriousNode l)) ρ :=
    (analyticAt_dyadicCoupling ρ).div (analyticAt_id.sub analyticAt_const) hden
  have hi := analyticAt_dyadicCouplingInv h2
  have hev : (fun z => dyadicCoupling z / (z - spuriousNode l) * dyadicCouplingInv z)
      =ᶠ[𝓝 ρ] (fun z => (z - spuriousNode l)⁻¹) := by
    filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds h2] with z hz
    unfold dyadicCouplingInv
    have hn : dyadicCoupling z ≠ 0 := two_cpow_neg_ne_half hz
    field_simp
  unfold normalizedFermiJet
  rw [dyadicForm_sum_right]
  · simp only [Complex.conj_conj, dyadicForm_spurious_logPower l _ hp]
    calc
      _ = iteratedDeriv j
          ((fun z => dyadicCoupling z / (z - spuriousNode l)) * dyadicCouplingInv) ρ := by
        rw [iteratedDeriv_mul hq.contDiffAt hi.contDiffAt]
        exact Finset.sum_congr rfl fun r _ => by ring
      _ = iteratedDeriv j (fun z => (z - spuriousNode l)⁻¹) ρ := hev.iteratedDeriv_eq j
      _ = _ := iteratedDeriv_shifted_inv j _ _
  · exact isFermiNymanWitness_spurious (by omega)
  · intro r hr
    apply isFermiNymanWitness_logPower_of_order h1 h2 r
    exact le_trans (by exact_mod_cast Nat.add_le_add_right (Nat.le_of_lt_succ (Finset.mem_range.1 hr)) 1) hj

end RHTower
