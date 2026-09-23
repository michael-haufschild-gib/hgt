import GaloisForLFunctions.RHTower.LiCarrierPairPhase
import GaloisForLFunctions.RHTower.GammaInvGrowth

/-!
# Li coefficients of the reflected-Gamma critical-line carrier

The reflected-Gamma carrier has one critical-line Schwarz pair at each height `alpha + k`.  This
module defines its divisor-normalized Li coefficient as the convergent sum of the squared-chord
pair contributions.  Splitting at the degree gives an explicit linear upper bound.  A full block
of `n` ordinates in the fixed phase chamber gives the matching linear lower bound.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Divisor-normalized Li coefficient of the reflected-Gamma arithmetic progression carrier. -/
def liReflectedGammaCarrierCoefficient (alpha : ℝ) (n : ℕ) : ℝ :=
  ∑' k : ℕ, liCarrierPairContribution n (alpha + k)

/-- A summable reciprocal-square majorant uniform in the progression shift `alpha > 0`. -/
theorem liCarrierPairContribution_le_natMajorant {alpha : ℝ} (halpha : 0 < alpha)
    (n k : ℕ) :
    liCarrierPairContribution n (alpha + k) ≤
      4 * (n : ℝ) ^ (2 : ℕ) / ((k : ℝ) + 1) ^ (2 : ℕ) := by
  have hgamma : alpha + (k : ℝ) ≠ 0 := by positivity
  have hquad := liCarrierPairContribution_le_quadratic
    (n := n) (gamma := alpha + k) hgamma
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hgammaLower : (k : ℝ) ≤ alpha + k := by linarith
  have hsquares : (k : ℝ) ^ (2 : ℕ) ≤ (alpha + k) ^ (2 : ℕ) := by nlinarith
  have hden : ((k : ℝ) + 1) ^ (2 : ℕ) / 4 ≤ (alpha + k) ^ (2 : ℕ) + 1 / 4 := by
    cases k with
    | zero => norm_num; positivity
    | succ k =>
        have hk1 : (1 : ℝ) ≤ (Nat.succ k : ℕ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
        nlinarith
  have hleft : 0 < ((k : ℝ) + 1) ^ (2 : ℕ) / 4 := by positivity
  have hrecip : 1 / ((alpha + k) ^ (2 : ℕ) + 1 / 4) ≤
      4 / ((k : ℝ) + 1) ^ (2 : ℕ) := by
    have h := one_div_le_one_div_of_le hleft hden
    calc
      1 / ((alpha + k) ^ (2 : ℕ) + 1 / 4)
          ≤ 1 / (((k : ℝ) + 1) ^ (2 : ℕ) / 4) := h
      _ = 4 / ((k : ℝ) + 1) ^ (2 : ℕ) := by
        field_simp
  calc
    liCarrierPairContribution n (alpha + k)
        ≤ (n : ℝ) ^ (2 : ℕ) / ((alpha + k) ^ (2 : ℕ) + 1 / 4) := hquad
    _ ≤ 4 * (n : ℝ) ^ (2 : ℕ) / ((k : ℝ) + 1) ^ (2 : ℕ) := by
      have hmul := mul_le_mul_of_nonneg_left hrecip (sq_nonneg (n : ℝ))
      calc
        (n : ℝ) ^ (2 : ℕ) / ((alpha + k) ^ (2 : ℕ) + 1 / 4) =
            (n : ℝ) ^ (2 : ℕ) * (1 / ((alpha + k) ^ (2 : ℕ) + 1 / 4)) := by ring
        _ ≤ (n : ℝ) ^ (2 : ℕ) * (4 / ((k : ℝ) + 1) ^ (2 : ℕ)) := hmul
        _ = 4 * (n : ℝ) ^ (2 : ℕ) / ((k : ℝ) + 1) ^ (2 : ℕ) := by ring

/-- Absolute summability of the complete critical-line pair contribution series. -/
theorem summable_liCarrierPairContribution {alpha : ℝ} (halpha : 0 < alpha)
    (n : ℕ) : Summable (fun k : ℕ => liCarrierPairContribution n (alpha + k)) := by
  have hp : Summable (fun k : ℕ => 1 / (k : ℝ) ^ (2 : ℕ)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ (2 : ℕ)) := by
    have h := (summable_nat_add_iff 1).mpr hp
    simpa [Nat.cast_add] using h
  have hmajor : Summable (fun k : ℕ =>
      4 * (n : ℝ) ^ (2 : ℕ) / ((k : ℝ) + 1) ^ (2 : ℕ)) := by
    have h := hshift.mul_left (4 * (n : ℝ) ^ (2 : ℕ))
    exact h.congr (fun k => by ring)
  refine Summable.of_norm_bounded hmajor ?_
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (liCarrierPairContribution_nonneg n (alpha + k))]
  exact liCarrierPairContribution_le_natMajorant halpha n k

/-- Every carrier coefficient is nonnegative. -/
theorem liReflectedGammaCarrierCoefficient_nonneg {alpha : ℝ} (n : ℕ) :
    0 ≤ liReflectedGammaCarrierCoefficient alpha n := by
  exact tsum_nonneg fun k => liCarrierPairContribution_nonneg n (alpha + k)

/-- Every positive-degree reflected-Gamma carrier coefficient is strictly positive. -/
theorem liReflectedGammaCarrierCoefficient_pos {alpha : ℝ} (halpha : 0 < alpha)
    {n : ℕ} (hn : 1 ≤ n) :
    0 < liReflectedGammaCarrierCoefficient alpha n := by
  have hs := summable_liCarrierPairContribution halpha n
  apply hs.tsum_pos (fun k => liCarrierPairContribution_nonneg n (alpha + k)) n
  apply liCarrierPairContribution_pos_of_degree_le_height hn
  · positivity
  · norm_num
    linarith

/-- Card equation `(20)`, with the explicit universal choice `C_alpha^+ = 12`. -/
theorem liReflectedGammaCarrierCoefficient_upper {alpha : ℝ} (halpha : 0 < alpha)
    {n : ℕ} (hn : 1 ≤ n) :
    liReflectedGammaCarrierCoefficient alpha n ≤ 12 * (n : ℝ) := by
  let f : ℕ → ℝ := fun k => liCarrierPairContribution n (alpha + k)
  have hs : Summable f := summable_liCarrierPairContribution halpha n
  have hsplit := hs.sum_add_tsum_nat_add (n + 1)
  have hhead : ∑ k ∈ Finset.range (n + 1), f k ≤ 4 * ((n : ℝ) + 1) := by
    calc
      ∑ k ∈ Finset.range (n + 1), f k ≤
          ∑ _k ∈ Finset.range (n + 1), (4 : ℝ) := by
            apply Finset.sum_le_sum
            intro k hk
            exact liCarrierPairContribution_le_four (by positivity : alpha + (k : ℝ) ≠ 0)
      _ = 4 * ((n : ℝ) + 1) := by simp; ring
  let g : ℕ → ℝ := fun k =>
    4 * (n : ℝ) ^ (2 : ℕ) / (((k + (n + 1) : ℕ) : ℝ) + 1) ^ (2 : ℕ)
  have htailPoint : ∀ k : ℕ, f (k + (n + 1)) ≤ g k := by
    intro k
    have h := liCarrierPairContribution_le_natMajorant halpha n (k + (n + 1))
    simpa [f, g, add_assoc] using h
  have hgSummable : Summable g := by
    have hp : Summable (fun k : ℕ => 1 / (k : ℝ) ^ (2 : ℕ)) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have hshiftOne : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ (2 : ℕ)) := by
      have h := (summable_nat_add_iff 1).mpr hp
      simpa [Nat.cast_add] using h
    have hbase := (summable_nat_add_iff (n + 1)).mpr hshiftOne
    have hmul := hbase.mul_left (4 * (n : ℝ) ^ (2 : ℕ))
    exact hmul.congr (fun k => by simp only [g, Nat.cast_add]; ring)
  have htailTsum : (∑' k : ℕ, f (k + (n + 1))) ≤ ∑' k : ℕ, g k :=
    ((summable_nat_add_iff (n + 1)).mpr hs).tsum_le_tsum htailPoint hgSummable
  have hrecip := HilbertSchmidt.tsum_reciprocal_square_tail_le (m := n + 1)
    (by omega : 1 ≤ n + 1)
  have hgBound : (∑' k : ℕ, g k) ≤ 4 * (n : ℝ) := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    calc
      (∑' k : ℕ, g k) = 4 * (n : ℝ) ^ (2 : ℕ) *
          (∑' k : ℕ, 1 / ((((k + (n + 1) : ℕ) : ℝ)) + 1) ^ (2 : ℕ)) := by
            simp only [g, div_eq_mul_inv]
            rw [tsum_mul_left]
            simp only [one_mul]
      _ ≤ 4 * (n : ℝ) ^ (2 : ℕ) * (1 / ((n + 1 : ℕ) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa [add_comm, add_left_comm, add_assoc] using hrecip
      _ ≤ 4 * (n : ℝ) := by
        rw [Nat.cast_add, Nat.cast_one]
        have hinv : 1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) :=
          one_div_le_one_div_of_le hnpos (by linarith)
        have hmul := mul_le_mul_of_nonneg_left hinv
          (by positivity : 0 ≤ 4 * (n : ℝ) ^ (2 : ℕ))
        calc
          4 * (n : ℝ) ^ (2 : ℕ) * (1 / ((n : ℝ) + 1)) ≤
              4 * (n : ℝ) ^ (2 : ℕ) * (1 / (n : ℝ)) := hmul
          _ = 4 * (n : ℝ) := by field_simp
  rw [liReflectedGammaCarrierCoefficient]
  change ∑' k : ℕ, f k ≤ _
  rw [← hsplit]
  have htail := htailTsum.trans hgBound
  have hncast : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

/-- Card equation `(23)`, lower half, with an explicit positive constant. -/
theorem liReflectedGammaCarrierCoefficient_lower {alpha : ℝ} (halpha : 0 < alpha)
    {n : ℕ} (hn : 1 ≤ n) (halphaN : alpha ≤ n) :
    (2 - 2 * Real.cos (1 / 6)) * (n : ℝ) ≤
      liReflectedGammaCarrierCoefficient alpha n := by
  let f : ℕ → ℝ := fun k => liCarrierPairContribution n (alpha + k)
  have hs : Summable f := summable_liCarrierPairContribution halpha n
  have hsplit := hs.sum_add_tsum_nat_add n
  have hshiftSummable : Summable (fun k : ℕ => f (k + n)) :=
    (summable_nat_add_iff n).mpr hs
  have hblockTsum : ∑ k ∈ Finset.range n, f (k + n) ≤
      ∑' k : ℕ, f (k + n) := by
    exact hshiftSummable.sum_le_tsum (Finset.range n)
      (fun k hk => by
        dsimp [f]
        exact liCarrierPairContribution_nonneg n (alpha + ((k + n : ℕ) : ℝ)))
  have hblock : (2 - 2 * Real.cos (1 / 6)) * (n : ℝ) ≤
      ∑ k ∈ Finset.range n, f (k + n) := by
    calc
      (2 - 2 * Real.cos (1 / 6)) * (n : ℝ) =
          ∑ _k ∈ Finset.range n, (2 - 2 * Real.cos (1 / 6)) := by simp; ring
      _ ≤ ∑ k ∈ Finset.range n, f (k + n) := by
        apply Finset.sum_le_sum
        intro k hk
        apply liCarrierPairContribution_lower_on_band hn
        · rw [Nat.cast_add]
          have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          nlinarith
        · rw [Nat.cast_add]
          have hklt : k < n := Finset.mem_range.mp hk
          have hkcast : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.le_of_lt hklt)
          nlinarith
  rw [liReflectedGammaCarrierCoefficient]
  change _ ≤ ∑' k : ℕ, f k
  rw [← hsplit]
  have hhead : 0 ≤ ∑ k ∈ Finset.range n, f k := by
    exact Finset.sum_nonneg fun k hk => liCarrierPairContribution_nonneg n (alpha + k)
  linarith

/-- Explicit two-sided linear carrier law for every degree beyond the fixed progression shift. -/
theorem liReflectedGammaCarrierCoefficient_twoSided {alpha : ℝ} (halpha : 0 < alpha)
    {n : ℕ} (hn : 1 ≤ n) (halphaN : alpha ≤ n) :
    (2 - 2 * Real.cos (1 / 6)) * (n : ℝ) ≤
        liReflectedGammaCarrierCoefficient alpha n ∧
      liReflectedGammaCarrierCoefficient alpha n ≤ 12 * (n : ℝ) :=
  ⟨liReflectedGammaCarrierCoefficient_lower halpha hn halphaN,
    liReflectedGammaCarrierCoefficient_upper halpha hn⟩

/-- Explicit positive margin valid uniformly over every positive Li degree. -/
def liReflectedGammaCarrierUniformMargin (alpha : ℝ) : ℝ :=
  2 - 2 * Real.cos (1 / (2 * (alpha + 1)))

/-- The explicit uniform carrier margin is strictly positive for `alpha > 0`. -/
theorem liReflectedGammaCarrierUniformMargin_pos {alpha : ℝ} (halpha : 0 < alpha) :
    0 < liReflectedGammaCarrierUniformMargin alpha := by
  have hdelta : 0 < 1 / (2 * (alpha + 1)) := by positivity
  have hdeltaPi : 1 / (2 * (alpha + 1)) < Real.pi := by
    have hdeltaHalf : 1 / (2 * (alpha + 1)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity : 0 < 2 * (alpha + 1))
        (by norm_num : (0 : ℝ) < 2)]
      nlinarith
    nlinarith [Real.pi_gt_three]
  have hcos := Real.strictAntiOn_cos
    (Set.mem_Icc.mpr ⟨by norm_num, Real.pi_pos.le⟩)
    (Set.mem_Icc.mpr ⟨hdelta.le, hdeltaPi.le⟩) hdelta
  rw [Real.cos_zero] at hcos
  unfold liReflectedGammaCarrierUniformMargin
  linarith

/-- Card equation `(24)`, constructive form: one fixed positive margin bounds every coefficient. -/
theorem liReflectedGammaCarrierUniformMargin_le {alpha : ℝ} (halpha : 0 < alpha)
    {n : ℕ} (hn : 1 ≤ n) :
    liReflectedGammaCarrierUniformMargin alpha ≤
      liReflectedGammaCarrierCoefficient alpha n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  let gamma : ℝ := alpha + n
  have hgamma : 0 < gamma := by dsimp [gamma]; positivity
  have hdegree : (n : ℝ) ≤ gamma := by dsimp [gamma]; linarith
  have hphaseLower := inv_two_mul_le_liCarrierPhase hgamma (by
    dsimp [gamma]
    have hncast : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith)
  have hangleLower : 1 / (2 * (alpha + 1)) ≤
      (n : ℝ) * liCarrierPhase gamma := by
    have hratio : 1 / (2 * (alpha + 1)) ≤
        (n : ℝ) / (2 * (alpha + n)) := by
      rw [div_le_div_iff₀ (by positivity : 0 < 2 * (alpha + 1))
        (by positivity : 0 < 2 * (alpha + n))]
      have hncast : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have hratio' : 1 / (2 * (alpha + 1)) ≤
        (n : ℝ) * (1 / (2 * gamma)) := by
      simpa [gamma, div_eq_mul_inv, one_div] using hratio
    exact hratio'.trans (mul_le_mul_of_nonneg_left hphaseLower hnpos.le)
  have hangleUpper : (n : ℝ) * liCarrierPhase gamma ≤ 1 := by
    calc
      (n : ℝ) * liCarrierPhase gamma ≤ (n : ℝ) * (1 / gamma) :=
        mul_le_mul_of_nonneg_left (liCarrierPhase_le_inv hgamma) hnpos.le
      _ ≤ 1 := by
        have hbase : (n : ℝ) / gamma ≤ 1 := (div_le_one hgamma).2 hdegree
        simpa [div_eq_mul_inv, one_div] using hbase
  have hpi : (1 : ℝ) ≤ Real.pi := by nlinarith [Real.pi_gt_three]
  have hcos : Real.cos ((n : ℝ) * liCarrierPhase gamma) ≤
      Real.cos (1 / (2 * (alpha + 1))) := by
    have hdelta : 0 < 1 / (2 * (alpha + 1)) := by positivity
    exact Real.antitoneOn_cos
      ⟨by positivity, by nlinarith [Real.pi_gt_three]⟩
      ⟨hdelta.le.trans hangleLower, hangleUpper.trans hpi⟩ hangleLower
  have hpair : liReflectedGammaCarrierUniformMargin alpha ≤
      liCarrierPairContribution n gamma := by
    rw [liCarrierPairContribution_eq_cos hgamma]
    unfold liReflectedGammaCarrierUniformMargin
    linarith
  have hs := summable_liCarrierPairContribution halpha n
  have hterm : liCarrierPairContribution n (alpha + n) ≤
      liReflectedGammaCarrierCoefficient alpha n := by
    rw [liReflectedGammaCarrierCoefficient]
    have h := hs.sum_le_tsum {n}
      (fun k hk => liCarrierPairContribution_nonneg n (alpha + k))
    simpa using h
  exact hpair.trans (by simpa [gamma] using hterm)

/-- Literal infimum of all positive-degree reflected-Gamma carrier coefficients. -/
def liReflectedGammaCarrierMarginInf (alpha : ℝ) : ℝ :=
  sInf {x : ℝ | ∃ n : ℕ, 1 ≤ n ∧ x = liReflectedGammaCarrierCoefficient alpha n}

/-- Card equation `(24)`: the literal all-degree carrier margin infimum is positive. -/
theorem liReflectedGammaCarrierMarginInf_pos {alpha : ℝ} (halpha : 0 < alpha) :
    0 < liReflectedGammaCarrierMarginInf alpha := by
  have hnonempty : {x : ℝ | ∃ n : ℕ, 1 ≤ n ∧
      x = liReflectedGammaCarrierCoefficient alpha n}.Nonempty := by
    exact ⟨liReflectedGammaCarrierCoefficient alpha 1, 1, by omega, rfl⟩
  have hlower : liReflectedGammaCarrierUniformMargin alpha ≤
      liReflectedGammaCarrierMarginInf alpha := by
    apply le_csInf hnonempty
    intro b hb
    obtain ⟨n, hn, rfl⟩ := hb
    exact liReflectedGammaCarrierUniformMargin_le halpha hn
  exact (liReflectedGammaCarrierUniformMargin_pos halpha).trans_le hlower

end

end RHTower
