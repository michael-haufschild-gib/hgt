import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.NewtonExtrapolationOfTheModularEnergy

/-!
# Isolating one radiation interval from finitely many Laplace samples

The multiplier 1 − (x − t)² fixes the mass at t. Every other release node
contracts uniformly when t = exp(−j). Its nth power needs only 2n+1
consecutive moments. This gives direct upper bounds for each individual
release, with explicit truncation and observation errors.
-/

open Finset Filter Topology
namespace GaloisForLFunctions.BlackHoleRingdown

noncomputable section

/-- Reading from the moments at k through k+2n of the multiplier (1−(x−t)²)ⁿ. -/
def releaseFilter (t : ℝ) (f : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, k => f k
  | n+1, k => (1-t^2)*releaseFilter t f n k + 2*t*releaseFilter t f n (k+1)
      - releaseFilter t f n (k+2)

private def multiplier (t x : ℝ) := 1-(x-t)^2

private theorem multiplier_nn {t x : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    (hx : 0 ≤ x) (hx' : x ≤ 1) : 0 ≤ multiplier t x := by
  have h : |x-t| ≤ 1 := abs_le.mpr ⟨by linarith only [ht',hx],by linarith only [ht,hx']⟩
  have hh := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs,one_pow] at hh
  exact sub_nonneg.mpr hh

private theorem multiplier_le (t x : ℝ) : multiplier t x ≤ 1 := sub_le_self _ (sq_nonneg _)

private def filteredMass (h : CompactPulse) (t : ℝ) (n k i : ℕ) :=
  multiplier t (radiationNode i)^n * (radiationNode i^k * stepDecrement h i 1)

private theorem filtered_hasSum (h : CompactPulse) (t : ℝ)
    (n k : ℕ) : HasSum (filteredMass h t n k) (releaseFilter t (radiationSample h) n k) := by
  induction n generalizing k with
  | zero =>
    have H := (summable_radiation_kernel h k 0).hasSum
    simpa only [filteredMass,pow_zero,one_mul,mul_one,releaseFilter,radiationSample] using H
  | succ n ih =>
    refine ((((ih k).mul_left (1-t^2)).add ((ih (k+1)).mul_left (2*t))).sub (ih (k+2))).congr_fun ?_
    intro i
    simp only [filteredMass,multiplier,pow_succ]
    ring

private theorem node_anti : Antitone radiationNode := by
  intro a b h
  exact Real.exp_le_exp.mpr (neg_le_neg (Nat.cast_le.mpr h))

private theorem node_succ (i : ℕ) : radiationNode (i+1) = radiationNode i*radiationNode 1 := by
  simp only [radiationNode,Nat.cast_add_one,Nat.cast_one,neg_add_rev,Real.exp_add,mul_comm]

/-- Distance from a release node to its nearest distinct node, on its right in time. -/
def releaseGap (j : ℕ) := radiationNode j*(1-radiationNode 1)

private theorem gap_pos (j : ℕ) : 0 < releaseGap j :=
  mul_pos (radiationNode_pos j) (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num)))

private theorem gap_le_one (j : ℕ) : releaseGap j ≤ 1 :=
  mul_le_one₀ (radiationNode_le_one j) (sub_nonneg.mpr (radiationNode_le_one 1))
    (sub_le_self _ (radiationNode_pos 1).le)

private theorem gap_le_distance {i j : ℕ} (hne : i ≠ j) :
    releaseGap j ≤ |radiationNode i-radiationNode j| := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hs := node_anti (show i+1 ≤ j by omega)
    rw [node_succ] at hs
    have hm := mul_le_mul_of_nonneg_right (node_anti h.le) (sub_nonneg.mpr (radiationNode_le_one 1))
    rw [abs_of_nonneg (sub_nonneg.mpr (node_anti h.le))]
    unfold releaseGap
    linarith only [hs,hm]
  · have hs := node_anti (show j+1 ≤ i by omega)
    rw [node_succ] at hs
    rw [abs_of_nonpos (sub_nonpos.mpr (node_anti h.le))]
    unfold releaseGap
    linarith only [hs]

/-- Uniform contraction away from the chosen interval. -/
def releaseContraction (j : ℕ) := 1-(releaseGap j)^2

private theorem contraction_bounds (j : ℕ) : 0 ≤ releaseContraction j ∧ releaseContraction j < 1 :=
  ⟨sub_nonneg.mpr (pow_le_one₀ (gap_pos j).le (gap_le_one j)),sub_lt_self _ (sq_pos_of_pos (gap_pos j))⟩

/-- A finite prefix gives an upper bound for exactly one unit release. The geometric
error uses only the total energy and the known spacing of its node. -/
theorem releaseFilter_enclosure (h : CompactPulse) (j n : ℕ) :
    stepDecrement h j 1 ≤ releaseFilter (radiationNode j) (radiationSample h) n 0 ∧
    releaseFilter (radiationNode j) (radiationSample h) n 0 ≤
      stepDecrement h j 1 + releaseContraction j^n * tailEnergy h 0 := by
  let t := radiationNode j
  let q := releaseContraction j
  let a (i : ℕ) := stepDecrement h i 1
  have hF := filtered_hasSum h (radiationNode j) n 0
  have hS : HasSum (fun i : ℕ => if i=j then a j else 0) (a j) := hasSum_ite_eq j _
  have hA : HasSum a (tailEnergy h 0) := by simpa [a] using unit_decrements_have_sum h 0
  have hq := (contraction_bounds j).1
  have hnn (i : ℕ) := multiplier_nn (radiationNode_pos j).le (radiationNode_le_one j)
    (radiationNode_pos i).le (radiationNode_le_one i)
  have hdiag : filteredMass h t n 0 j = a j := by simp [filteredMass,t,multiplier,a]
  constructor
  · apply hasSum_le _ hS hF
    intro i
    by_cases hi : i=j
    · subst i
      simpa only [if_true] using hdiag.ge
    · simp only [if_neg hi,filteredMass,pow_zero,one_mul]
      exact mul_nonneg (pow_nonneg (hnn i) _) (stepDecrement_nonneg _ _ _)
  · apply hasSum_le _ hF (hS.add (hA.mul_left (q^n)))
    intro i
    by_cases hi : i=j
    · subst i
      change filteredMass h t n 0 j ≤ (if j=j then a j else 0)+q^n*a j
      rw [hdiag,if_pos rfl]
      exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg hq _) (stepDecrement_nonneg _ _ _))
    · have hg := pow_le_pow_left₀ (gap_pos j).le (gap_le_distance hi) 2
      rw [sq_abs] at hg
      have hh : multiplier t (radiationNode i) ≤ q := sub_le_sub_left hg 1
      change filteredMass h t n 0 i ≤ (if i=j then a j else 0)+q^n*a i
      simp only [if_neg hi,zero_add,filteredMass,pow_zero,one_mul]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hnn i) hh _) (stepDecrement_nonneg _ _ _)

/-- No prior release values are needed to recover the energy of interval j. -/
theorem releaseFilter_tendsto (h : CompactPulse) (j : ℕ) :
    Tendsto (fun n => releaseFilter (radiationNode j) (radiationSample h) n 0) atTop (𝓝 (stepDecrement h j 1)) := by
  have hq := contraction_bounds j
  have hz := (tendsto_pow_atTop_nhds_zero_of_lt_one hq.1 hq.2).mul_const (tailEnergy h 0)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using (tendsto_const_nhds (x := stepDecrement h j 1)).add hz)
    (fun n => (releaseFilter_enclosure h j n).1) (fun n => (releaseFilter_enclosure h j n).2)

/-- Observation error on the first 2n+1 readings costs at most a factor 3ⁿ,
uniformly in the selected node. -/
theorem releaseFilter_stability (f g : ℕ → ℝ) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    (n k : ℕ) {ε : ℝ} (he : 0 ≤ ε) (h : ∀ i, k ≤ i → i ≤ k+2*n → |f i-g i| ≤ ε) :
    |releaseFilter t f n k-releaseFilter t g n k| ≤ (3:ℝ)^n*ε := by
  induction n generalizing k with
  | zero => simpa only [releaseFilter,pow_zero,one_mul] using h k le_rfl (by omega)
  | succ n ih =>
    let B := (3:ℝ)^n*ε
    have hB : 0 ≤ B := mul_nonneg (by positivity) he
    have h₀ := ih k (fun i hl hu => h i hl (by omega))
    have h₁ := ih (k+1) (fun i hl hu => h i (by omega) (by omega))
    have h₂ := ih (k+2) (fun i hl hu => h i (by omega) (by omega))
    let D (k : ℕ) := releaseFilter t f n k-releaseFilter t g n k
    have hb : 0 ≤ 1-t^2 := sub_nonneg.mpr (pow_le_one₀ ht ht')
    change |D k| ≤ B at h₀
    change |D (k+1)| ≤ B at h₁
    change |D (k+2)| ≤ B at h₂
    have heq : releaseFilter t f (n+1) k-releaseFilter t g (n+1) k =
        (1-t^2)*D k+2*t*D (k+1)-D (k+2) := by dsimp only [releaseFilter,D]; ring
    rw [heq,pow_succ]
    calc _ ≤ |(1-t^2)*D k|+|2*t*D (k+1)|+|D (k+2)| :=
            (abs_sub _ _).trans (add_le_add_right (abs_add_le ..) _)
         _ ≤ (1-t^2)*B+2*t*B+B := by
            simp only [abs_mul,abs_of_nonneg hb,abs_of_nonneg (show 0 ≤ 2*t by positivity)]
            exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left h₀ hb)
              (mul_le_mul_of_nonneg_left h₁ (by positivity))) h₂
         _ ≤ _ := by
            have H := mul_nonneg (sq_nonneg (1-t)) hB
            change _ ≤ 3^n*3*ε
            calc _ ≤ 3*B := by linarith only [H]
                 _ = _ := by dsimp only [B]; ring


end

end GaloisForLFunctions.BlackHoleRingdown
