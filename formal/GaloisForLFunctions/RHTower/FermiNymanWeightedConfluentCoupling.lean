import GaloisForLFunctions.RHTower.FermiNymanWeightedSignature

/-!
# Weighted logarithmic source coupling

Weighted cutoff Mellin transforms are translations by `2a-1` of the original ones.
Differentiation gives all logarithmic moments. Normalizing by the actual weighted
source numerator produces exact confluent Cauchy columns at the translated spurious
nodes. All pairings below are literal weighted integrals.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

/-- The source numerator retained by the matched weighted form. -/
def weightedDyadicCoupling (a : ℝ) (z : ℂ) : ℂ :=
  (2 : ℂ) ^ ((1 : ℂ) - (2 * a : ℝ)) * dyadicCoupling z

def weightedDyadicCouplingInv (a : ℝ) (z : ℂ) : ℂ := (weightedDyadicCoupling a z)⁻¹

theorem analyticAt_weightedDyadicCoupling (a : ℝ) (z : ℂ) :
    AnalyticAt ℂ (weightedDyadicCoupling a) z :=
  analyticAt_const.mul (analyticAt_dyadicCoupling z)

theorem weightedDyadicCoupling_ne_zero (a : ℝ) {z : ℂ} (hz : z.re < 1) :
    weightedDyadicCoupling a z ≠ 0 :=
  mul_ne_zero (Complex.cpow_ne_zero_iff.2 (Or.inl (by norm_num)))
    (by exact two_cpow_neg_ne_half hz)

theorem analyticAt_weightedDyadicCouplingInv (a : ℝ) {z : ℂ} (hz : z.re < 1) :
    AnalyticAt ℂ (weightedDyadicCouplingInv a) z :=
  (analyticAt_weightedDyadicCoupling a z).inv (weightedDyadicCoupling_ne_zero a hz)

theorem mellin_logWeighted_spuriousCut_weighted (a : ℝ) (k : ℤ) (c : ℝ) (j : ℕ) (ρ : ℂ) :
    mellin (logWeighted (spuriousCut k c) j) (ρ + (2 * a - 1 : ℝ)) =
      ∫ t in Ioc (0 : ℝ) c, (t ^ (2 * a - 1) : ℝ) * spuriousWitness k t *
        (starRingEnd ℂ) (logPowerWitness ((starRingEnd ℂ) ρ) j t) := by
  rw [mellin_logWeighted_spuriousCut]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  have h := congrArg (fun z : ℂ => ((Real.log t : ℂ) ^ j) * z)
    (weighted_powerWitness_pair a k ρ ht.1)
  simp only [logPowerWitness, map_mul, map_pow, Complex.conj_ofReal]
  linear_combination -h

theorem weightedDyadicForm_spurious_logPower (a : ℝ) (l j : ℕ) {ρ : ℂ}
    (hρ : 0 < ρ.re + 2 * a - 1) :
    weightedDyadicForm a (spuriousWitness ((l : ℤ) + 1))
      (logPowerWitness ((starRingEnd ℂ) ρ) j) =
      iteratedDeriv j (fun z => weightedDyadicCoupling a z / (z - weightedSpuriousNode a l)) ρ := by
  let k : ℤ := (l : ℤ) + 1
  let δ : ℂ := (2 * a - 1 : ℝ)
  let C : ℂ := ((2 : ℝ) ^ (-2 * a) : ℝ)
  let F : ℂ → ℂ := fun z => mellin (spuriousCut k (1 / 2)) (z + δ) -
    C * mellin (spuriousCut k 1) (z + δ)
  have hhalf := mellinRapid_spuriousCut k (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hone := mellinRapid_spuriousCut k zero_lt_one le_rfl
  have hshift : 0 < (ρ + δ).re := by
    simp only [δ, Complex.add_re, Complex.ofReal_re]
    linarith
  have hHa : AnalyticAt ℂ (fun z => mellin (spuriousCut k (1 / 2)) (z + δ)) ρ := (hhalf.analyticAt_mellin hshift).comp (f := fun z : ℂ => z + δ) (x := ρ) (analyticAt_id.add analyticAt_const)
  have hOa : AnalyticAt ℂ (fun z => mellin (spuriousCut k 1) (z + δ)) ρ := (hone.analyticAt_mellin hshift).comp (f := fun z : ℂ => z + δ) (x := ρ) (analyticAt_id.add analyticAt_const)
  have hF : ∀ z : ℂ, 0 < z.re + 2 * a - 1 →
      F z = weightedDyadicCoupling a z / (z - weightedSpuriousNode a l) := by
    intro z hz
    change mellin (spuriousCut k (1 / 2)) (z + δ) -
      C * mellin (spuriousCut k 1) (z + δ) = _
    rw [← show logWeighted (spuriousCut k (1 / 2)) 0 = spuriousCut k (1 / 2) from
      funext (logWeighted_zero _),
      ← show logWeighted (spuriousCut k 1) 0 = spuriousCut k 1 from funext (logWeighted_zero _),
      mellin_logWeighted_spuriousCut_weighted, mellin_logWeighted_spuriousCut_weighted]
    simp only [logPowerWitness, pow_zero, one_mul]
    change weightedDyadicForm a (spuriousWitness k) (powerWitness ((starRingEnd ℂ) z)) = _
    rw [weightedDyadicForm_spurious_power a k hz]
    unfold weightedDyadicCoupling weightedSpuriousNode spuriousNode k
    congr 1
    push_cast
    ring
  have hev : F =ᶠ[𝓝 ρ]
      (fun z => weightedDyadicCoupling a z / (z - weightedSpuriousNode a l)) := by
    filter_upwards [(isOpen_lt continuous_const
      ((Complex.continuous_re.add continuous_const).sub continuous_const)).mem_nhds hρ] with z hz
    exact hF z hz
  rw [← hev.iteratedDeriv_eq j]
  change _ = iteratedDeriv j
    ((fun z => mellin (spuriousCut k (1 / 2)) (z + δ)) -
      ((fun _ : ℂ => C) * (fun z => mellin (spuriousCut k 1) (z + δ)))) ρ
  rw [iteratedDeriv_sub hHa.contDiffAt (analyticAt_const.mul hOa).contDiffAt]
  change _ = iteratedDeriv j (fun z => mellin (spuriousCut k (1 / 2)) (z + δ)) ρ -
    iteratedDeriv j (fun z => C * mellin (spuriousCut k 1) (z + δ)) ρ
  rw [iteratedDeriv_const_mul_field]
  simp only [iteratedDeriv_comp_add_const]
  rw [iteratedDeriv_mellin hhalf j hshift,
    iteratedDeriv_mellin hone j hshift, mellin_logWeighted_spuriousCut_weighted,
    mellin_logWeighted_spuriousCut_weighted]
  rfl

theorem weightedDyadicForm_sum_left {a : ℝ} {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℂ) (c : ι → ℂ) {v : ℝ → ℂ} (hv : IsWeightedFermiWitness a v)
    (hf : ∀ i ∈ s, IsWeightedFermiWitness a (f i)) :
    weightedDyadicForm a (fun t => ∑ i ∈ s, c i * f i t) v =
      ∑ i ∈ s, c i * weightedDyadicForm a (f i) v := by
  have hexp : ∀ t, (t ^ (2 * a - 1) : ℝ) *
      (∑ i ∈ s, c i * f i t) * (starRingEnd ℂ) (v t) =
      ∑ i ∈ s, c i * ((t ^ (2 * a - 1) : ℝ) * f i t * (starRingEnd ℂ) (v t)) := by
    intro t
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hI : ∀ S : Set ℝ, S ⊆ Ioc (0 : ℝ) 1 →
      (∫ t in S, (t ^ (2 * a - 1) : ℝ) * (∑ i ∈ s, c i * f i t) * (starRingEnd ℂ) (v t)) =
        ∑ i ∈ s, c i * ∫ t in S, (t ^ (2 * a - 1) : ℝ) * f i t * (starRingEnd ℂ) (v t) := by
    intro S hS
    simp_rw [hexp]
    rw [integral_finsetSum _ (fun i hi =>
      (((hf i hi).integrableOn_weighted_mul_conj hv).mono_set hS).const_mul _)]
    exact Finset.sum_congr rfl (fun _ _ => integral_const_mul _ _)
  unfold weightedDyadicForm
  rw [hI _ (Ioc_subset_Ioc_right (by norm_num)), hI _ subset_rfl,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem weightedDyadicForm_sum_right {a : ℝ} {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (c : ι → ℂ) {v : ℝ → ℂ} (hv : IsWeightedFermiWitness a v)
    (hf : ∀ i ∈ s, IsWeightedFermiWitness a (f i)) :
    weightedDyadicForm a v (fun t => ∑ i ∈ s, c i * f i t) =
      ∑ i ∈ s, (starRingEnd ℂ) (c i) * weightedDyadicForm a v (f i) := by
  rw [weightedDyadicForm_conj, weightedDyadicForm_sum_left s f c hv hf, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← weightedDyadicForm_conj]


/-- Logarithmic source jets divided by the weighted source numerator. -/
def weightedNormalizedFermiJet (a : ℝ) (ρ : ℂ) (j : ℕ) (t : ℝ) : ℂ :=
  ∑ r ∈ Finset.range (j + 1),
    (starRingEnd ℂ) ((j.choose r : ℂ) * iteratedDeriv (j - r) (weightedDyadicCouplingInv a) ρ) *
      logPowerWitness ((starRingEnd ℂ) ρ) r t

theorem isWeightedFermiWitness_weightedNormalizedFermiJet {a : ℝ} (ha1 : a < 1) {ρ : ℂ}
    (h1 : 1 - a < ρ.re) (h2 : ρ.re < 1) (j : ℕ)
    (hj : ((j + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt riemannZeta ρ) :
    IsWeightedFermiWitness a (weightedNormalizedFermiJet a ρ j) := by
  apply isWeightedFermiWitness_finsetSum ha1 (Finset.range (j + 1))
    (fun r => logPowerWitness ((starRingEnd ℂ) ρ) r)
    (fun r => (starRingEnd ℂ) ((j.choose r : ℂ) *
      iteratedDeriv (j - r) (weightedDyadicCouplingInv a) ρ)) (fun r hr => ?_)
  apply isWeightedFermiWitness_logPower_of_order ha1 h1 h2 r
  exact le_trans (by
    exact_mod_cast Nat.add_le_add_right (Nat.le_of_lt_succ (Finset.mem_range.1 hr)) 1) hj

theorem weightedDyadicForm_spurious_weightedNormalizedFermiJet {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (l j : ℕ) {ρ : ℂ}
    (h1 : 1 - a < ρ.re) (h2 : ρ.re < 1)
    (hj : ((j + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt riemannZeta ρ) :
    weightedDyadicForm a (spuriousWitness ((l : ℤ) + 1)) (weightedNormalizedFermiJet a ρ j) =
      (-1 : ℂ) ^ j * (j.factorial : ℂ) * ((ρ - weightedSpuriousNode a l)⁻¹) ^ (j + 1) := by
  have hp : 0 < ρ.re + 2 * a - 1 := by linarith
  have hden : ρ - weightedSpuriousNode a l ≠ 0 := by
    intro h
    have h' := congrArg Complex.re (sub_eq_zero.1 h)
    rw [weightedSpuriousNode_re] at h'
    linarith
  have hq : AnalyticAt ℂ (fun z => weightedDyadicCoupling a z / (z - weightedSpuriousNode a l)) ρ :=
    (analyticAt_weightedDyadicCoupling a ρ).div (analyticAt_id.sub analyticAt_const) hden
  have hi := analyticAt_weightedDyadicCouplingInv a h2
  have hev : (fun z => weightedDyadicCoupling a z / (z - weightedSpuriousNode a l) * (weightedDyadicCouplingInv a) z)
      =ᶠ[𝓝 ρ] (fun z => (z - weightedSpuriousNode a l)⁻¹) := by
    filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds h2] with z hz
    unfold weightedDyadicCouplingInv
    have hn : weightedDyadicCoupling a z ≠ 0 := weightedDyadicCoupling_ne_zero a hz
    field_simp
  unfold weightedNormalizedFermiJet
  rw [weightedDyadicForm_sum_right]
  · simp only [Complex.conj_conj, weightedDyadicForm_spurious_logPower a l _ hp]
    calc
      _ = iteratedDeriv j
          ((fun z => weightedDyadicCoupling a z / (z - weightedSpuriousNode a l)) * (weightedDyadicCouplingInv a)) ρ := by
        rw [iteratedDeriv_mul hq.contDiffAt hi.contDiffAt]
        exact Finset.sum_congr rfl fun r _ => by ring
      _ = iteratedDeriv j (fun z => (z - weightedSpuriousNode a l)⁻¹) ρ := hev.iteratedDeriv_eq j
      _ = _ := iteratedDeriv_shifted_inv j _ _
  · exact isWeightedFermiWitness_spurious ha0 (by omega)
  · intro r hr
    apply isWeightedFermiWitness_logPower_of_order ha1 h1 h2 r
    exact le_trans (by exact_mod_cast Nat.add_le_add_right (Nat.le_of_lt_succ (Finset.mem_range.1 hr)) 1) hj

end RHTower
