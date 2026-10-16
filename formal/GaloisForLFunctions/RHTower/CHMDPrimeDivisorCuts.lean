import GaloisForLFunctions.RHTower.WeilPhiDoobDivisorEnergy
import GaloisForLFunctions.RHTower.WeilPhiDoobReflectedKillingPotentialAndDisjointSupportDiagonal

/-!
# Positive divisor cuts of the original prime-jump source

Fold each jump crossing the origin before grouping the two theta indices and
its prime-power index by their product N. Only divisor edges m | k | N with
log m < u < log k survive. Their common theta fiber is strictly positive on
this interval, so every finite cut density is nonnegative independently.
The complete crossing series is absolutely convergent and equals the sum of
these cut integrals, with every prime power and both theta indices retained.

The full Doob source splits into the archimedean jump energy, two same-side
prime energies, and these positive cuts, minus the original cosh mass.
The cut sum has trivial nullspace on continuous compactly supported tests:
arbitrarily long powers-of-two jumps force any null vector outside its support.
No comparison with the cosh mass, CHMD defect elimination, or RH is asserted.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators

noncomputable section
namespace RHTower.CHMDPrimeCuts
open PhiDivisorEnergy

/-- Only divisor edges straddling the logarithmic cut are retained. -/
def divisorCutEnergy (N : ℕ) (u : ℝ) (a : ℕ → ℝ) : ℝ :=
  ∑ k ∈ N.divisors, ∑ m ∈ k.divisors,
    if u ∈ Ioo (Real.log m) (Real.log k) then
      ArithmeticFunction.vonMangoldt (k / m) * (a m - a k) ^ 2 else 0

def cutDensity (N : ℕ) (v : ℝ → ℝ) (u : ℝ) : ℝ :=
  fiber N u * divisorCutEnergy N u (fun m => v (u - Real.log m))

def cutEdge (v : ℝ → ℝ) (m d n : ℕ) : ℝ → ℝ :=
  (Ioo (Real.log m) (Real.log (m * d : ℕ))).indicator (edge v m d n)

def primeCrossing (v : ℝ → ℝ) (d : ℕ) : ℝ :=
  ∫ x in Ioo (0 : ℝ) (Real.log d), phiDoobPrimeJump v d (x - Real.log d)

theorem divisorCutEnergy_nonneg (N : ℕ) (u : ℝ) (a : ℕ → ℝ) :
    0 ≤ divisorCutEnergy N u a := by
  unfold divisorCutEnergy
  apply Finset.sum_nonneg
  intro k hk
  apply Finset.sum_nonneg
  intro m hm
  split_ifs
  · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (sq_nonneg _)
  · rfl

theorem divisorCutEnergy_zero_outside {N : ℕ} {u : ℝ}
    (hu : u ∉ Ioo (0 : ℝ) (Real.log N)) (a : ℕ → ℝ) :
    divisorCutEnergy N u a = 0 := by
  unfold divisorCutEnergy
  apply Finset.sum_eq_zero
  intro k hk
  apply Finset.sum_eq_zero
  intro m hm
  have hnot : u ∉ Ioo (Real.log m) (Real.log k) := by
    intro h
    apply hu
    have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_mem_divisors hk
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast Nat.divisor_le hk
    exact ⟨lt_of_le_of_lt (Real.log_natCast_nonneg m) h.1,
      lt_of_lt_of_le h.2 (Real.log_le_log hk0 hkN)⟩
  simp only [if_neg hnot]

theorem fiber_pos_on_central {N : ℕ} (hN : 0 < N) {u : ℝ}
    (hu : 0 ≤ u) (huN : u ≤ Real.log N) : 0 < fiber N u := by
  have h1 := cuspTerm_riemannCuspPoly_pos (n := 1) (by omega) hu
  have h2 := cuspTerm_riemannCuspPoly_pos (n := 1) (by omega)
    (show 0 ≤ -u + Real.log N by linarith)
  have he := cuspTerm_add_log riemannCuspPoly 1 hN (-u)
  simp only [Nat.mul_one] at he
  rw [he] at h2
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hNterm : 0 < cuspTerm riemannCuspPoly N (-u) := (mul_pos_iff_of_pos_left hs).mp h2
  exact mul_pos h1 hNterm

theorem cutDensity_zero_outside {N : ℕ} {u : ℝ}
    (hu : u ∉ Ioo (0 : ℝ) (Real.log N)) (v : ℝ → ℝ) : cutDensity N v u = 0 := by
  rw [cutDensity, divisorCutEnergy_zero_outside hu, mul_zero]

/-- Each arithmetic product index is nonnegative separately; no signed theta tail remains. -/
theorem cutDensity_nonneg (N : ℕ+) (v : ℝ → ℝ) (u : ℝ) : 0 ≤ cutDensity N v u := by
  by_cases hu : u ∈ Ioo (0 : ℝ) (Real.log (N : ℕ))
  · exact mul_nonneg (fiber_pos_on_central N.pos hu.1.le hu.2.le).le
      (divisorCutEnergy_nonneg _ _ _)
  · rw [cutDensity_zero_outside hu]

theorem integrable_cutEdge {v : ℝ → ℝ} (hv : Continuous v) {M : ℝ}
    (hM : 0 ≤ M) (hvM : ∀ u, |v u| ≤ M) (m d n : ℕ+) :
    Integrable (cutEdge v m d n) :=
  (integrable_edge hv hM hvM m d n).indicator measurableSet_Ioo

theorem norm_cutEdge_le (v : ℝ → ℝ) (m d n : ℕ) (u : ℝ) :
    ‖cutEdge v m d n u‖ ≤ ‖edge v m d n u‖ := by
  by_cases hu : u ∈ Ioo (Real.log m) (Real.log (m * d : ℕ))
  · simp only [cutEdge, indicator_of_mem hu, le_refl]
  · simp only [cutEdge, indicator_of_notMem hu, norm_zero, norm_nonneg]

theorem summable_integral_norm_cutEdge {v : ℝ → ℝ} (hv : Continuous v) {M : ℝ}
    (hM : 0 ≤ M) (hvM : ∀ u, |v u| ≤ M) :
    Summable (fun p : (ℕ+ × ℕ+) × ℕ+ => ∫ u, ‖cutEdge v p.1.1 p.1.2 p.2 u‖) := by
  apply (summable_integral_norm_edge hv hM hvM).of_nonneg_of_le
    (fun p => integral_nonneg fun u => norm_nonneg _)
  intro p
  exact integral_mono (integrable_cutEdge hv hM hvM p.1.1 p.1.2 p.2).norm
    (integrable_edge hv hM hvM p.1.1 p.1.2 p.2).norm (norm_cutEdge_le v _ _ _)

theorem summable_integral_cutEdge {v : ℝ → ℝ} (hv : Continuous v) {M : ℝ}
    (hM : 0 ≤ M) (hvM : ∀ u, |v u| ≤ M) :
    Summable (fun p : (ℕ+ × ℕ+) × ℕ+ => ∫ u, cutEdge v p.1.1 p.1.2 p.2 u) :=
  (summable_integral_norm_cutEdge hv hM hvM).of_norm_bounded
    (fun _ => norm_integral_le_integral_norm _)

theorem cutEdge_shift (v : ℝ → ℝ) {m d n : ℕ} (hm : 0 < m) (hd : 0 < d) (x : ℝ) :
    cutEdge v m d n (x + Real.log m) =
      (Ioo (0 : ℝ) (Real.log d)).indicator
        (fun y => edge v m d n (y + Real.log m)) x := by
  have hl : Real.log (m * d : ℕ) = Real.log m + Real.log d := by
    rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  have he : x + Real.log m ∈ Ioo (Real.log m) (Real.log (m * d : ℕ)) ↔
      x ∈ Ioo (0 : ℝ) (Real.log d) := by
    rw [hl]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  by_cases hx : x ∈ Ioo (0 : ℝ) (Real.log d)
  · rw [cutEdge, indicator_of_mem (he.mpr hx), indicator_of_mem hx]
  · rw [cutEdge, indicator_of_notMem (mt he.mp hx), indicator_of_notMem hx]

theorem tsum_shifted_cutEdge (v : ℝ → ℝ) (d : ℕ+) (x : ℝ) :
    (∑' p : ℕ+ × ℕ+, cutEdge v p.1 d p.2 (x + Real.log (p.1 : ℕ))) =
      (Ioo (0 : ℝ) (Real.log (d : ℕ))).indicator
        (fun y => phiDoobPrimeJump v d (y - Real.log (d : ℕ))) x := by
  simp_rw [cutEdge_shift v (PNat.pos _) d.pos]
  by_cases hx : x ∈ Ioo (0 : ℝ) (Real.log (d : ℕ))
  · simp only [indicator_of_mem hx]
    exact tsum_shifted_edge_eq v d x
  · simp only [indicator_of_notMem hx, tsum_zero]

theorem primeCrossing_eq_tsum_edges {v : ℝ → ℝ} (hv : Continuous v) {M : ℝ}
    (hM : 0 ≤ M) (hvM : ∀ u, |v u| ≤ M) (d : ℕ+) :
    primeCrossing v d = ∑' p : ℕ+ × ℕ+, ∫ u, cutEdge v p.1 d p.2 u := by
  have hs := primeFirstEquiv.summable_iff.mpr (summable_integral_norm_cutEdge hv hM hvM)
  change Summable (fun q : ℕ+ × (ℕ+ × ℕ+) =>
    ∫ u, ‖cutEdge v q.2.1 q.1 q.2.2 u‖) at hs
  have hd : Summable (fun p : ℕ+ × ℕ+ =>
      ∫ x, ‖cutEdge v p.1 d p.2 (x + Real.log (p.1 : ℕ))‖) :=
    (hs.prod_factor d).congr (fun p =>
      (integral_add_right_eq_self (fun u => ‖cutEdge v p.1 d p.2 u‖)
        (Real.log (p.1 : ℕ))).symm)
  have hi := integral_tsum_of_summable_integral_norm
    (fun p : ℕ+ × ℕ+ => (integrable_cutEdge hv hM hvM p.1 d p.2).comp_add_right
      (Real.log (p.1 : ℕ))) hd
  simp_rw [tsum_shifted_cutEdge, integral_add_right_eq_self] at hi
  rw [integral_indicator measurableSet_Ioo] at hi
  exact hi.symm

theorem cutDensity_eq_sum_edges (v : ℝ → ℝ) (N : ℕ) (u : ℝ) :
    cutDensity N v u =
      ∑ c ∈ N.divisorsAntidiagonal, ∑ q ∈ c.1.divisorsAntidiagonal,
        cutEdge v q.1 q.2 c.2 u := by
  rw [Nat.sum_divisorsAntidiagonal (fun k n =>
    ∑ q ∈ k.divisorsAntidiagonal, cutEdge v q.1 q.2 n u)]
  unfold cutDensity divisorCutEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.sum_divisorsAntidiagonal (fun m d => cutEdge v m d (N / k) u), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [cutEdge, indicator_apply, edge, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hm),
    Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hk)]
  split_ifs <;> ring

theorem integral_cutDensity_eq {v : ℝ → ℝ} (hv : Continuous v) {M : ℝ}
    (hM : 0 ≤ M) (hvM : ∀ u, |v u| ≤ M) (N : ℕ) :
    (∫ u, cutDensity N v u) =
      ∑ c ∈ N.divisorsAntidiagonal, ∑ q ∈ c.1.divisorsAntidiagonal,
        ∫ u, cutEdge v q.1 q.2 c.2 u := by
  have hi (c : ℕ × ℕ) (hc : c ∈ N.divisorsAntidiagonal)
      (q : ℕ × ℕ) (hq : q ∈ c.1.divisorsAntidiagonal) : Integrable (cutEdge v q.1 q.2 c.2) :=
    integrable_cutEdge hv hM hvM
      ⟨q.1, Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hq)⟩
      ⟨q.2, Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hq)⟩
      ⟨c.2, Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hc)⟩
  simp_rw [cutDensity_eq_sum_edges]
  rw [integral_finsetSum _ (fun c hc => integrable_finsetSum _ (hi c hc))]
  apply Finset.sum_congr rfl
  intro c hc
  exact integral_finsetSum _ (hi c hc)

theorem primeCrossing_hasSum_cuts {v : ℝ → ℝ} (hv : Continuous v) {M : ℝ}
    (hM : 0 ≤ M) (hvM : ∀ u, |v u| ≤ M) :
    HasSum (fun N : ℕ+ => ∫ u, cutDensity N v u) (∑' d : ℕ+, primeCrossing v d) := by
  have hs := summable_integral_cutEdge hv hM hvM
  have hp := primeFirstEquiv.summable_iff.mpr hs
  change Summable (fun q : ℕ+ × (ℕ+ × ℕ+) => ∫ u, cutEdge v q.2.1 q.1 q.2.2 u) at hp
  have ht : (∑' d : ℕ+, primeCrossing v d) =
      ∑' p : (ℕ+ × ℕ+) × ℕ+, ∫ u, cutEdge v p.1.1 p.1.2 p.2 u := by
    simp_rw [primeCrossing_eq_tsum_edges hv hM hvM]
    rw [← hp.tsum_prod]
    exact primeFirstEquiv.tsum_eq (fun p => ∫ u, cutEdge v p.1.1 p.1.2 p.2 u)
  rw [ht]
  simpa only [integral_cutDensity_eq hv hM hvM] using
    hasSum_chains (F := fun m d n => ∫ u, cutEdge v m d n u) hs

def sameSide (v : ℝ → ℝ) : ℝ :=
  ∑' d : ℕ, ∫ x in Ioi (0 : ℝ), phiDoobPrimeJump v d x

theorem integrable_primeJump {v : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) (d : ℕ) : Integrable (phiDoobPrimeJump v d) := by
  have he : phiDoobPrimeJump v d = phiDoobPrimeDiagonal v d - phiDoobPrimeCross v d :=
    funext (phiDoobPrimeJump_eq_diagonal_sub_cross v d)
  rw [he]
  exact (integrable_phiDoobPrimeDiagonal hv hvc d).sub
    (integrable_phiDoobPrimeCross hv hvc d)

/-- Split a jump into its two same-side pieces and its origin-crossing piece. -/
theorem integral_primeJump_split {v : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) (d : ℕ) :
    (∫ x, phiDoobPrimeJump v d x) =
      (∫ x in Ioi (0 : ℝ), phiDoobPrimeJump v d x) +
      (∫ x in Ioi (0 : ℝ), phiDoobPrimeJump (fun y => v (-y)) d x) +
      primeCrossing v d := by
  let t : ℝ := Real.log d
  let g : ℝ → ℝ := fun x => phiDoobPrimeJump v d (-x)
  have ht : 0 ≤ t := Real.log_natCast_nonneg d
  have hint := integrable_primeJump hv hvc d
  have hsplit := integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hint
  rw [compl_Iic] at hsplit
  have hneg : (∫ x in Iic (0 : ℝ), phiDoobPrimeJump v d x) =
      ∫ x in Ioi (0 : ℝ), g x := by
    simpa only [neg_zero, integral_Iic_eq_integral_Iio, g] using
      (integral_comp_neg_Ioi (c := (0 : ℝ)) (phiDoobPrimeJump v d)).symm
  have hgi : IntegrableOn g (Ioi (0 : ℝ)) := hint.comp_neg.integrableOn
  have hparts : (∫ x in Ioi (0 : ℝ), g x) =
      (∫ x in Ioo (0 : ℝ) t, g x) + ∫ x in Ioi t, g x := by
    rw [← Ioc_union_Ioi_eq_Ioi ht,
      setIntegral_union (Ioc_disjoint_Ioi (le_refl t)) measurableSet_Ioi
        (hgi.mono_set Ioc_subset_Ioi_self) (hgi.mono_set (Ioi_subset_Ioi ht)),
      integral_Ioc_eq_integral_Ioo]
  have hcollar : (∫ x in Ioo (0 : ℝ) t, g x) = primeCrossing v d := by
    rw [← setIntegral_Ioo_reflect_self g t]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    change phiDoobPrimeJump v d (-(t - x)) = phiDoobPrimeJump v d (x - t)
    congr 1; ring
  have htail : (∫ x in Ioi t, g x) =
      ∫ x in Ioi (0 : ℝ), phiDoobPrimeJump (fun y => v (-y)) d x := by
    have hmp : MeasurePreserving (fun x : ℝ => x + t) volume volume :=
      measurePreserving_add_right volume t
    have hemb := (Homeomorph.addRight t).measurableEmbedding
    have hpre : (fun x : ℝ => x + t) ⁻¹' Ioi t = Ioi (0 : ℝ) := by
      ext x
      simp
    have htr := hmp.setIntegral_preimage_emb hemb g (Ioi t)
    rw [hpre] at htr
    rw [← htr]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change phiDoobPrimeJump v d (-(x + t)) =
      phiDoobPrimeJump (fun y => v (-y)) d x
    unfold phiDoobPrimeJump
    rw [show -(x + t) + Real.log d = -x by dsimp [t]; ring]
    simp only [riemannKernelReal_neg_eq]
    dsimp [t]
    ring
  rw [hneg, hparts, hcollar, htail] at hsplit
  linarith

theorem primeCrossing_nonneg (v : ℝ → ℝ) (d : ℕ) : 0 ≤ primeCrossing v d :=
  setIntegral_nonneg measurableSet_Ioo (fun _ _ => phiDoobPrimeJump_nonneg v d _)

theorem summable_sameSide {v : ℝ → ℝ} (hv : Continuous v) (hvc : HasCompactSupport v) :
    Summable (fun d : ℕ => ∫ x in Ioi (0 : ℝ), phiDoobPrimeJump v d x) := by
  apply (summable_integral_phiDoobPrimeJump hv hvc).of_nonneg_of_le
    (fun d => setIntegral_nonneg measurableSet_Ioi fun x _ => phiDoobPrimeJump_nonneg v d x)
  intro d
  exact setIntegral_le_integral (integrable_primeJump hv hvc d)
    (Eventually.of_forall (phiDoobPrimeJump_nonneg v d))

theorem sameSide_nonneg (v : ℝ → ℝ) : 0 ≤ sameSide v :=
  tsum_nonneg (fun d => setIntegral_nonneg measurableSet_Ioi fun x _ =>
    phiDoobPrimeJump_nonneg v d x)

theorem summable_primeCrossing {v : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) : Summable (primeCrossing v) := by
  apply (summable_integral_phiDoobPrimeJump hv hvc).of_nonneg_of_le (primeCrossing_nonneg v)
  intro d
  calc
    primeCrossing v d ≤ ∫ x, phiDoobPrimeJump v d (x - Real.log d) :=
      setIntegral_le_integral ((integrable_primeJump hv hvc d).comp_sub_right _)
        (Eventually.of_forall fun x => phiDoobPrimeJump_nonneg v d _)
    _ = ∫ x, phiDoobPrimeJump v d x := integral_sub_right_eq_self _ _

theorem primeCrossing_nat_eq_pnat {v : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) :
    (∑' d : ℕ, primeCrossing v d) = ∑' d : ℕ+, primeCrossing v d := by
  have hs := (summable_nat_add_iff 1).mpr (summable_primeCrossing hv hvc)
  rw [tsum_eq_zero_add' hs]
  have h0 : primeCrossing v 0 = 0 := by simp [primeCrossing]
  rw [h0, zero_add]
  exact Equiv.pnatEquivNat.symm.tsum_eq (fun d : ℕ+ => primeCrossing v d)

/-- Every prime power and both theta indices survive in the positive cut expansion. -/
theorem primeJump_eq_sameSide_add_cuts_of_bounded {v : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) {M : ℝ} (hM : 0 ≤ M) (hvM : ∀ u, |v u| ≤ M) :
    (∑' d : ℕ, ∫ x, phiDoobPrimeJump v d x) =
      sameSide v + sameSide (fun x => v (-x)) + ∑' N : ℕ+, ∫ u, cutDensity N v u := by
  have hvr : Continuous (fun x => v (-x)) := hv.comp continuous_neg
  have hvrc : HasCompactSupport (fun x => v (-x)) := hvc.comp_homeomorph (Homeomorph.neg ℝ)
  simp_rw [integral_primeJump_split hv hvc]
  rw [Summable.tsum_add ((summable_sameSide hv hvc).add (summable_sameSide hvr hvrc))
      (summable_primeCrossing hv hvc),
    Summable.tsum_add (summable_sameSide hv hvc) (summable_sameSide hvr hvrc),
    primeCrossing_nat_eq_pnat hv hvc, ← (primeCrossing_hasSum_cuts hv hM hvM).tsum_eq]
  rfl

/-- Compact support supplies the bound needed by the complete theta reindexing. -/
theorem compact_primeCrossing_hasSum_cuts {v : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) :
    HasSum (fun N : ℕ+ => ∫ u, cutDensity N v u) (∑' d : ℕ, primeCrossing v d) := by
  obtain ⟨M, hM⟩ := hvc.exists_bound_of_continuous hv
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (v 0)) (hM 0)
  rw [primeCrossing_nat_eq_pnat hv hvc]
  exact primeCrossing_hasSum_cuts hv hM0 (by simpa only [Real.norm_eq_abs] using hM)

theorem primeJump_eq_sameSide_add_cuts {v : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) :
    (∑' d : ℕ, ∫ x, phiDoobPrimeJump v d x) =
      sameSide v + sameSide (fun x => v (-x)) + ∑' N : ℕ+, ∫ u, cutDensity N v u := by
  obtain ⟨M, hM⟩ := hvc.exists_bound_of_continuous hv
  exact primeJump_eq_sameSide_add_cuts_of_bounded hv hvc
    (le_trans (norm_nonneg (v 0)) (hM 0)) (by simpa only [Real.norm_eq_abs] using hM)

/-- Exact original source identity. The cosh mass is retained with its negative sign. -/
theorem doob_source_eq_positive_cuts_sub_cosh {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) :
    markovEnergy (fun x => (phiDoobTest v x : ℂ)) =
      phiDoobArchJumpEnergy v + sameSide v + sameSide (fun x => v (-x)) +
        (∑' N : ℕ+, ∫ u, cutDensity N v u) - phiDoobCoshMass (fun x => v x ^ 2) := by
  rw [phiDoob_markovEnergy_eq_archJump_add_primeJump_sub_coshMass hv hvc,
    primeJump_eq_sameSide_add_cuts hv.continuous hvc]
  ring

/-- A zero crossing integral forces equality across its entire closed collar. -/
theorem collar_eq_of_primeCrossing_zero {v : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) {d : ℕ} (hd : 0 < vonMangoldtAtom d)
    (hlog : 0 < Real.log d) (hz : primeCrossing v d = 0) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (Real.log d)) : v (x - Real.log d) = v x := by
  have hc : Continuous (fun x => phiDoobPrimeJump v d (x - Real.log d)) := by
    have hc0 : Continuous (phiDoobPrimeJump v d) :=
      (((continuous_const.mul continuous_riemannKernelReal).mul
      (continuous_riemannKernelReal.comp (continuous_id.add continuous_const))).mul
      ((hv.sub (hv.comp (continuous_id.add continuous_const))).pow 2))
    exact hc0.comp (continuous_id.sub continuous_const)
  have hi := ((integrable_primeJump hv hvc d).comp_sub_right (Real.log d)).integrableOn
    (s := Ioo (0 : ℝ) (Real.log d))
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun x => phiDoobPrimeJump_nonneg v d (x - Real.log d)) hi).mp hz
  have he := (Measure.eqOn_open_of_ae_eq hae isOpen_Ioo hc.continuousOn
    continuous_zero.continuousOn).closure hc continuous_zero
  rw [closure_Ioo hlog.ne] at he
  have hj := he hx
  change vonMangoldtAtom d * riemannKernelReal (x - Real.log d) *
    riemannKernelReal (x - Real.log d + Real.log d) *
    (v (x - Real.log d) - v (x - Real.log d + Real.log d)) ^ 2 = 0 at hj
  rw [sub_add_cancel] at hj
  have hp : 0 < vonMangoldtAtom d * riemannKernelReal (x - Real.log d) * riemannKernelReal x :=
    mul_pos (mul_pos hd (riemannKernelReal_pos _)) (riemannKernelReal_pos _)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hj).resolve_left hp.ne'))

/-- Powers of two provide genuine prime jumps of arbitrarily large length. -/
theorem exists_positive_primeJump_after (B : ℝ) :
    ∃ d : ℕ, 0 < vonMangoldtAtom d ∧ max B 0 < Real.log d := by
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  obtain ⟨k, hk⟩ := exists_nat_gt (max B 0 / Real.log (2 : ℝ))
  refine ⟨2 ^ (k + 1), ?_, ?_⟩
  · have hd : 2 ≤ (2 : ℕ) ^ (k + 1) := by
      rw [pow_succ]
      have hp : 0 < (2 : ℕ) ^ k := by positivity
      omega
    rw [vonMangoldtAtom, if_pos hd, ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    exact div_pos h2 (Real.sqrt_pos.mpr (by positivity))
  · rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    have hkl : max B 0 < (k : ℝ) * Real.log 2 := (div_lt_iff₀ h2).mp hk
    push_cast
    nlinarith

/-- The positive crossing source has no nonzero compactly supported null vector. -/
theorem crossing_cuts_eq_zero_iff {v : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) :
    (∑' N : ℕ+, ∫ u, cutDensity N v u) = 0 ↔ v = 0 := by
  rw [(compact_primeCrossing_hasSum_cuts hv hvc).tsum_eq]
  constructor
  · intro hz
    have hterm (d : ℕ) : primeCrossing v d = 0 := by
      apply le_antisymm _ (primeCrossing_nonneg v d)
      calc
        primeCrossing v d ≤ ∑' n : ℕ, primeCrossing v n :=
          (summable_primeCrossing hv hvc).le_tsum d (fun n _ => primeCrossing_nonneg v n)
        _ = 0 := hz
    obtain ⟨R, hR⟩ := hvc.isBounded.exists_norm_le
    have hout {y : ℝ} (hy : R < |y|) : v y = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hys
      exact (not_le_of_gt hy) (by simpa only [Real.norm_eq_abs] using hR y hys)
    funext x
    obtain ⟨d, hd, hlog⟩ := exists_positive_primeJump_after (|x| + |R| + 1)
    have hL : |x| + |R| + 1 < Real.log d := lt_of_le_of_lt (le_max_left _ _) hlog
    have hL0 : 0 < Real.log d := lt_of_le_of_lt (le_max_right _ _) hlog
    have hxlo := neg_abs_le x
    have hxhi := le_abs_self x
    have hRhi := le_abs_self R
    by_cases hx : 0 ≤ x
    · have hc := collar_eq_of_primeCrossing_zero hv hvc hd hL0 (hterm d)
        (show x ∈ Icc (0 : ℝ) (Real.log d) by constructor <;> linarith [abs_nonneg R])
      have hy : R < |x - Real.log d| := by
        rw [abs_of_neg (by linarith [abs_nonneg R])]
        linarith
      exact hc.symm.trans (hout hy)
    · have hc := collar_eq_of_primeCrossing_zero hv hvc hd hL0 (hterm d)
        (show x + Real.log d ∈ Icc (0 : ℝ) (Real.log d) by
          constructor <;> linarith [abs_nonneg R])
      rw [add_sub_cancel_right] at hc
      have hy : R < |x + Real.log d| := by
        rw [abs_of_pos (by linarith [abs_nonneg R])]
        linarith
      exact hc.trans (hout hy)
  · rintro rfl
    simp [primeCrossing, phiDoobPrimeJump]

theorem crossing_cuts_pos {v : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) (hne : v ≠ 0) :
    0 < ∑' N : ℕ+, ∫ u, cutDensity N v u := by
  have hn : 0 ≤ ∑' N : ℕ+, ∫ u, cutDensity N v u :=
    tsum_nonneg (fun N => integral_nonneg (cutDensity_nonneg N v))
  exact lt_of_le_of_ne hn (Ne.symm (mt (crossing_cuts_eq_zero_iff hv hvc).mp hne))

end RHTower.CHMDPrimeCuts
