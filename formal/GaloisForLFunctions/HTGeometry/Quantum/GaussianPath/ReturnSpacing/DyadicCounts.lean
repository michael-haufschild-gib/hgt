import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.BoxMass
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.BlockCount
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PairedRows

/-! # Simultaneous isolated-field counts across dyadic scales -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical ENNReal
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private abbrev Block := PathPauliBlockLabel → ℝ

/-- For k = 2ʲ, the first k⁴⁸ independent pairs contain at least c k²⁴
isolated-field boxes eventually almost surely on a single infinite sample. -/
theorem gaussian_pauli_dyadic_box_counts :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ j : ℕ in atTop,
      let k : ℕ := 2^j
      c*(k:ℝ)^24 ≤ (((Finset.range (k^48)).filter
        (fun i => pathPauliBlock ω i ∈ isolatedFieldBox k)).card : ℝ) := by
  let μ : Measure Block := Measure.infinitePi fun _ => gaussianReal 0 1
  let ν : Measure (ℕ → Block) := Measure.infinitePi fun _ => μ
  haveI : IsProbabilityMeasure μ := by unfold μ; infer_instance
  have hpair : MeasurePreserving pathPauliBlock pathPauliDisorderLaw ν := measurePreserving_paired_rows _
  obtain ⟨d,hd,hmass⟩ := isolated_field_box_mass
  let bad (j : ℕ) : Set (ℕ → Block) :=
    let k : ℕ := 2^j
    {x | (((Finset.range (k^48)).filter (fun i => x i ∈ isolatedFieldBox k)).card : ℝ) <
      d/2*(k:ℝ)^24}
  have hrisk (j : ℕ) : ν (bad j) ≤ ENNReal.ofReal (4/d)*(2:ℝ≥0∞)⁻¹^j := by
    let k : ℕ := 2^j
    have hk : 1 ≤ (k:ℝ) := by exact_mod_cast (show 1 ≤ 2^j from Nat.succ_le_of_lt (pow_pos (by decide : 0 < (2:ℕ)) _))
    have hkp : 0 < (k:ℝ) := zero_lt_one.trans_le hk
    have hm : d*(k:ℝ)^24 ≤ ((k^48:ℕ):ℝ)*μ.real (isolatedFieldBox k) := by
      have h := hmass k hk
      change d/(k:ℝ)^24 ≤ μ.real (isolatedFieldBox k) at h
      have h' := (div_le_iff₀ (pow_pos hkp 24)).mp h
      push_cast
      calc
        _ ≤ (μ.real (isolatedFieldBox k)*(k:ℝ)^24)*(k:ℝ)^24 :=
          mul_le_mul_of_nonneg_right h' (by positivity)
        _ = _ := by ring
    have hpos := (mul_pos hd (pow_pos hkp 24)).trans_le hm
    have h := iid_box_count_lower_tail μ (measurableSet_isolatedFieldBox k) (k^48) hpos
    have hs : bad j ⊆ {ω : ℕ → Block | (((Finset.range (k^48)).filter
        (fun i => ω i ∈ isolatedFieldBox k)).card : ℝ) < ((k^48:ℕ):ℝ)*μ.real (isolatedFieldBox k)/2} := by
      intro x hx
      change _ < d/2*(k:ℝ)^24 at hx
      exact hx.trans_le (by linarith only [hm])
    refine ((measure_mono hs).trans h).trans ?_
    have hkpow : (k:ℝ) ≤ (k:ℝ)^24 := by simpa using pow_le_pow_right₀ hk (show 1 ≤ 24 by decide)
    have hr : 4/(((k^48:ℕ):ℝ)*μ.real (isolatedFieldBox k)) ≤ (4/d)*(2⁻¹:ℝ)^j := by
      have hlow := (mul_le_mul_of_nonneg_left hkpow hd.le).trans hm
      calc
        _ ≤ 4/(d*(k:ℝ)) := div_le_div_of_nonneg_left (by norm_num) (mul_pos hd hkp) hlow
        _ = (4/d)*(2⁻¹:ℝ)^j := by simp [k,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]
    refine (ENNReal.ofReal_le_ofReal hr).trans_eq ?_
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<2)]
    norm_num
  have hBC : ∀ᵐ x ∂ν, ∀ᶠ j in atTop, x ∉ bad j := by
    apply ae_eventually_notMem
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hrisk)
    rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric_two]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)
  refine ⟨d/2,half_pos hd,?_⟩
  filter_upwards [hpair.quasiMeasurePreserving.ae hBC] with ω hω
  filter_upwards [hω] with j hj
  exact le_of_not_gt hj

/-- The same successful odd sites work on every longer prefix containing
these pairs, including prefixes ending midway between two dyadic scales. -/
theorem gaussian_pauli_dyadic_isolated_sites :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ j : ℕ in atTop,
      let k : ℕ := 2^j
      let q : ℝ := 1/(8*(k:ℝ))
      ∀ n : ℕ, 2*k^48 ≤ n+2 → ∃ S : Finset (Fin (n+2)), c*(k:ℝ)^24 ≤ S.card ∧
        ∀ s ∈ S, isolatedLongitudinalSite (pathPauliDisorderShell ω n) q (q/200) s := by
  obtain ⟨c,hc,hw⟩ := gaussian_pauli_dyadic_box_counts
  refine ⟨c,hc,?_⟩
  filter_upwards [hw] with ω hω
  filter_upwards [hω] with j hj
  let k : ℕ := 2^j
  let q : ℝ := 1/(8*(k:ℝ))
  let A := (Finset.range (k^48)).filter (fun i => pathPauliBlock ω i ∈ isolatedFieldBox k)
  intro _ _ n hn
  let g : {i // i ∈ A} ↪ Fin (n+2) := {
    toFun := fun i => ⟨2*i.val+1,by
      have h := Finset.mem_range.mp (Finset.mem_filter.mp i.2).1
      change 2*k^48 ≤ n+2 at hn
      omega⟩
    inj' := by intro a b hab; apply Subtype.ext
               have he := congrArg Fin.val hab
               change 2*a.val+1 = 2*b.val+1 at he; omega }
  refine ⟨A.attach.map g,by simpa only [Finset.card_map,Finset.card_attach] using hj,?_⟩
  intro s hs
  obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hs
  apply isolated_odd_site_of_block ω q (q/200) (j := i.val) rfl
  have h := Set.mem_univ_pi.mp (Finset.mem_filter.mp i.2).2
  intro a
  have ha := h a
  change isolatedFieldBlockCenter q a-q/200 ≤ _ ∧ _ ≤ isolatedFieldBlockCenter q a+q/200 at ha
  exact abs_le.mpr ⟨by linarith only [ha.1],by linarith only [ha.2]⟩

#print axioms gaussian_pauli_dyadic_isolated_sites
end
end GaloisForLFunctions.HTGeometry
