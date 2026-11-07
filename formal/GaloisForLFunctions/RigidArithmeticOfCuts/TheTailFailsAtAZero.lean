import GaloisForLFunctions.RigidArithmeticOfCuts.ZerosOfADirichletPolynomialRecurEffectively
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheTransportCountOfAZero
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.ReturnsAreReturnsOfThePrimes

/-!
# The tail fails at a zero

Why do primes recur at a zero, if they do? Three statements separate the primes from the tail.

* **The primes always recur.** For every finite family `P` and tolerance `η`, the heights at which all phases `p^{iτ}` return
  have positive lower density (`exists_density_primeReturnSet`). This uses effective Kronecker and nothing about `ζ`.
* **Above the abscissa the primes are enough.** For `Re s ≥ σ > 1` the tail is summable, so a return of the primes up to a
  length is a return of `ζ` on the whole half-plane (`primeReturnSet_subset_zetaReturnSet`).
* **At a zero the primes are not enough.** Let `ρ` be a zero with `½ < Re ρ < 1`. Returns of `ζ` on a disc around `ρ` have
  measure `O(T^θ)` with `θ < 1`, so at a positive proportion of heights all primes of `P` return and `ζ` does not
  (`exists_primeReturn_not_zetaReturn`). This holds for every `P`, whatever its length.

So no finite amount of prime recurrence gives recurrence of a zero. A bounded return must be a return of every prime, and the
tail is what fails. A Dirichlet polynomial has no tail, and its zeros recur in every window.
-/

open Complex Filter MeasureTheory Metric Set Topology
open RHTower
open GaloisForLFunctions.ArithmeticAuxiliaryDynamics

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-- The heights at which the primes of `P` return within `η`. -/
def primeReturnSet (P : Finset ℕ) (η : ℝ) : Set ℝ :=
  {τ | ∀ p ∈ P, 1 - Real.cos (τ * Real.log p) ≤ η}

/-- The chord is subadditive in its square. -/
theorem one_sub_cos_add_le (a b : ℝ) :
    1 - Real.cos (a + b) ≤ 2 * (1 - Real.cos a) + 2 * (1 - Real.cos b) := by
  rw [Real.cos_add]
  nlinarith [sq_nonneg (Real.sin a - Real.sin b), sq_nonneg (Real.cos a + Real.cos b - 2),
    Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b]

/-- **The primes always recur.** The heights at which a finite family of prime phases returns have positive lower density. -/
theorem exists_density_primeReturnSet {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {η : ℝ} (hη : 0 < η) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ T : ℝ in atTop,
      ENNReal.ofReal (c * T) ≤ volume (primeReturnSet P η ∩ Icc 0 T) := by
  classical
  obtain ⟨D, hD⟩ := exists_nat_gt (20 * (P.card : ℝ) / η)
  have hsmall : 5 * (P.card : ℝ) / ((D : ℝ) + 1) ≤ η / 4 := by
    rw [div_lt_iff₀ hη] at hD
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  set T₀ : ℝ := 4 * ((D : ℝ) + 1) * (radicalOf P : ℝ) ^ (D + 1) * ((exponentBox P D).card : ℝ) + 1 with hT₀
  have hT₀pos : 0 < T₀ := by rw [hT₀]; positivity
  set S : ℝ := ∑ p ∈ P, Real.log p + 1 with hS
  have hlogp : ∀ p ∈ P, 0 ≤ Real.log (p : ℝ) := fun p _ => Real.log_natCast_nonneg p
  have hSpos : 0 < S := by
    have : 0 ≤ ∑ p ∈ P, Real.log (p : ℝ) := Finset.sum_nonneg hlogp
    rw [hS]
    linarith
  have hplog : ∀ p ∈ P, Real.log (p : ℝ) ≤ S := fun p hp => by
    have := Finset.single_le_sum hlogp hp
    rw [hS]
    linarith
  set w : ℝ := Real.sqrt (η / 2) / S with hw
  have hw0 : 0 < w := div_pos (Real.sqrt_pos.mpr (by positivity)) hSpos
  have hwS : (w * S) ^ 2 = η / 2 := by
    rw [hw, div_mul_cancel₀ _ hSpos.ne', Real.sq_sqrt (by positivity)]
  set L : ℝ := T₀ + 2 * w with hL
  have hLpos : 0 < L := by rw [hL]; positivity
  refine ⟨w / L, div_pos hw0 hLpos, ?_⟩
  choose τ hτ hret using fun k : ℕ => exists_height_phase_return_window D hP (fun _ => 0) (fun _ => 1)
    (fun _ _ => zero_le_one) (T := T₀) (by rw [hT₀]; linarith) ((k : ℝ) * L + w)
  simp only [sub_zero, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] at hret
  -- Every point of the interval around a window return is a return.
  have hinterval : ∀ k t, t ∈ Ioo (τ k - w) (τ k + w) → t ∈ primeReturnSet P η := by
    intro k t ht p hp
    have hk : 1 - Real.cos (τ k * Real.log p) ≤ η / 4 := by
      have h1 := Finset.single_le_sum (s := P) (f := fun p : ℕ => 1 - Real.cos (τ k * Real.log (p : ℝ)))
        (fun q _ => by linarith [Real.cos_le_one (τ k * Real.log (q : ℝ))]) hp
      exact h1.trans ((hret k).trans hsmall)
    have hsplit : t * Real.log p = τ k * Real.log p + (t - τ k) * Real.log p := by ring
    have hh : |t - τ k| ≤ w := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hquad : 2 * (1 - Real.cos ((t - τ k) * Real.log p)) ≤ η / 2 := by
      have h1 := Real.one_sub_sq_div_two_le_cos (x := (t - τ k) * Real.log p)
      have h2 : ((t - τ k) * Real.log p) ^ 2 ≤ (w * S) ^ 2 := by
        rw [mul_pow, mul_pow]
        have h3 : (t - τ k) ^ 2 ≤ w ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hh 2
        have h4 : Real.log (p : ℝ) ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ (hlogp p hp) (hplog p hp) 2
        exact mul_le_mul h3 h4 (sq_nonneg _) (sq_nonneg _)
      rw [hwS] at h2
      linarith
    have := one_sub_cos_add_le (τ k * Real.log p) ((t - τ k) * Real.log p)
    rw [← hsplit] at this
    linarith
  have hkL : ∀ k : ℕ, (k : ℝ) * L ≤ τ k - w ∧ τ k + w ≤ ((k : ℝ) + 1) * L := fun k => by
    obtain ⟨h1, h2⟩ := hτ k
    constructor
    · linarith
    · have : ((k : ℝ) + 1) * L = (k : ℝ) * L + T₀ + 2 * w := by rw [hL]; ring
      linarith
  filter_upwards [eventually_ge_atTop (2 * L)] with T hT
  set n : ℕ := ⌊T / L⌋₊ with hn
  have hT0 : 0 ≤ T := by linarith
  have hnle : (n : ℝ) * L ≤ T := by
    have := Nat.floor_le (div_nonneg hT0 hLpos.le)
    rw [← hn, le_div_iff₀ hLpos] at this
    exact this
  have hnlo : T / (2 * L) ≤ (n : ℝ) := by
    have h1 := Nat.lt_floor_add_one (T / L)
    rw [← hn] at h1
    have h2 : 2 ≤ T / L := by rwa [le_div_iff₀ hLpos]
    have h3 : T / (2 * L) = (T / L) / 2 := by
      rw [div_div, mul_comm]
    rw [h3]
    linarith
  have hsub : (⋃ k ∈ Finset.range n, Ioo (τ k - w) (τ k + w)) ⊆ primeReturnSet P η ∩ Icc 0 T := by
    intro t ht
    obtain ⟨k, hk, htk⟩ := Set.mem_iUnion₂.mp ht
    refine ⟨hinterval k t htk, ?_, ?_⟩
    · have := (hkL k).1
      have hk0 : 0 ≤ (k : ℝ) * L := by positivity
      linarith [htk.1]
    · have hk1 : (k : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.mp hk
      have h1 : ((k : ℝ) + 1) * L ≤ (n : ℝ) * L := mul_le_mul_of_nonneg_right hk1 hLpos.le
      linarith [htk.2, (hkL k).2]
  have hdisj : (↑(Finset.range n) : Set ℕ).PairwiseDisjoint fun k => Ioo (τ k - w) (τ k + w) := by
    intro k _ l _ hkl
    refine Set.disjoint_left.mpr fun x hx hy => ?_
    rcases lt_or_gt_of_ne hkl with h | h
    · have h1 : (k : ℝ) + 1 ≤ l := by exact_mod_cast h
      have h2 : ((k : ℝ) + 1) * L ≤ (l : ℝ) * L := mul_le_mul_of_nonneg_right h1 hLpos.le
      linarith [hx.2, hy.1, (hkL k).2, (hkL l).1]
    · have h1 : (l : ℝ) + 1 ≤ k := by exact_mod_cast h
      have h2 : ((l : ℝ) + 1) * L ≤ (k : ℝ) * L := mul_le_mul_of_nonneg_right h1 hLpos.le
      linarith [hx.1, hy.2, (hkL l).2, (hkL k).1]
  have hvol : volume (⋃ k ∈ Finset.range n, Ioo (τ k - w) (τ k + w)) =
      ENNReal.ofReal ((n : ℝ) * (2 * w)) := by
    rw [measure_biUnion_finset hdisj fun _ _ => measurableSet_Ioo]
    have hk : ∀ k ∈ Finset.range n, volume (Ioo (τ k - w) (τ k + w)) = ENNReal.ofReal (2 * w) := fun k _ => by
      rw [Real.volume_Ioo]
      congr 1
      ring
    rw [Finset.sum_congr rfl hk, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  refine le_trans ?_ (measure_mono hsub)
  rw [hvol]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : w / L * T = 2 * w * (T / (2 * L)) := by
    field_simp
  rw [h1, mul_comm ((n : ℝ))]
  exact mul_le_mul_of_nonneg_left hnlo (by positivity)

/-- **At a zero the primes are not enough.** At a zero right of the line there is a tolerance `ε` such that, for every
finite family of primes and every `η`, at a positive proportion of heights all the primes return within `η` and `ζ` does
not return within `ε` on the disc. -/
theorem exists_primeReturn_not_zetaReturn {ρ : ℂ} (hz : riemannZeta ρ = 0) (h1 : 1 / 2 < ρ.re) (h2 : ρ.re < 1)
    {r : ℝ} (hr : 0 < r) (hA : 1 / 2 < ρ.re - 2 * r) (hB : ρ.re + 2 * r < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → ∀ η : ℝ, 0 < η →
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ T : ℝ in atTop,
        ENNReal.ofReal (c * T) ≤
          volume ((primeReturnSet P η \ zetaReturnSet (closedBall ρ r) ε) ∩ Icc 0 T) := by
  obtain ⟨ε, hε, θ, hθ, hrare⟩ := (riemannZeta_eq_zero_iff_returnExponent h1 h2).mp hz r hr hA hB
  refine ⟨ε, hε, fun P hP η hη => ?_⟩
  obtain ⟨c, hc, hdense⟩ := exists_density_primeReturnSet hP hη
  refine ⟨c / 2, half_pos hc, ?_⟩
  have hpow : ∀ᶠ T : ℝ in atTop, T ^ θ ≤ c / 2 * T := by
    have hlim : Tendsto (fun T : ℝ => T ^ (θ - 1)) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (y := 1 - θ) (by linarith) |>.congr fun T => by
        rw [show θ - 1 = -(1 - θ) by ring]
    filter_upwards [hlim.eventually (gt_mem_nhds (half_pos hc)), eventually_gt_atTop 0] with T hT hT0
    have hval : T ^ θ = T ^ (θ - 1) * T := by
      rw [Real.rpow_sub_one hT0.ne']
      field_simp
    rw [hval]
    exact mul_le_mul_of_nonneg_right hT.le hT0.le
  filter_upwards [hdense, hrare, hpow, eventually_ge_atTop 0] with T hT1 hT2 hT3 hT4
  set A := primeReturnSet P η
  set B := zetaReturnSet (closedBall ρ r) ε
  have hsplit : A ∩ Icc 0 T ⊆ ((A \ B) ∩ Icc 0 T) ∪ (B ∩ Icc 0 T) := by
    rintro t ⟨htA, htI⟩
    by_cases htB : t ∈ B
    · exact Or.inr ⟨htB, htI⟩
    · exact Or.inl ⟨⟨htA, htB⟩, htI⟩
  have hle : ENNReal.ofReal (c * T) ≤ volume ((A \ B) ∩ Icc 0 T) + ENNReal.ofReal (c / 2 * T) := by
    calc ENNReal.ofReal (c * T) ≤ volume (A ∩ Icc 0 T) := hT1
      _ ≤ volume ((A \ B) ∩ Icc 0 T) + volume (B ∩ Icc 0 T) :=
          (measure_mono hsplit).trans (measure_union_le _ _)
      _ ≤ _ := by
          gcongr
          exact hT2.trans (ENNReal.ofReal_le_ofReal hT3)
  have hhalf : ENNReal.ofReal (c * T) = ENNReal.ofReal (c / 2 * T) + ENNReal.ofReal (c / 2 * T) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  rw [hhalf] at hle
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp hle

/-- **Above the abscissa the primes are enough.** On a half-plane `Re s ≥ σ > 1` a return of the primes up to a length is a
return of `ζ`, because the tail is summable. -/
theorem primeReturnSet_subset_zetaReturnSet {σ : ℝ} (hσ : 1 < σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ ∃ η : ℝ, 0 < η ∧
      primeReturnSet P η ⊆ zetaReturnSet {s : ℂ | σ ≤ s.re} ε := by
  classical
  set g : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-σ) with hg
  have hgs : Summable g := by
    have h := (Real.summable_nat_rpow (p := -σ)).mpr (by linarith)
    have h2 := (summable_nat_add_iff 1).mpr h
    refine h2.congr fun n => ?_
    simp [hg]
  have hg0 : ∀ n, 0 ≤ g n := fun n => by positivity
  have htail := tendsto_sum_nat_add g
  obtain ⟨N, hN⟩ := (htail.eventually (gt_mem_nhds (by positivity : 0 < ε / 8))).exists
  set P : Finset ℕ := (Finset.range (N + 2)).filter Nat.Prime with hPdef
  set A : ℝ := ∑ n ∈ Finset.range N, g n * (ArithmeticFunction.cardFactors (n + 1) : ℝ) with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun n _ => mul_nonneg (hg0 n) (Nat.cast_nonneg _)
  set δ : ℝ := ε / (4 * (A + 1)) with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hAδ : A * δ ≤ ε / 4 := by
    rw [hδ, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine ⟨P, fun p hp => (Finset.mem_filter.mp hp).2, δ ^ 2 / 2, by positivity, fun τ hτ s hs => ?_⟩
  have hs' : σ ≤ s.re := hs
  have hprime : ∀ p ∈ P, ‖phase τ p - 1‖ ≤ δ := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    have hsq := norm_phase_sub_one_sq τ hp'.pos
    have h1 := hτ p hp
    have h2 : ‖phase τ p - 1‖ ^ 2 ≤ δ ^ 2 := by
      rw [hsq]
      linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hδ0.le (by norm_num)).mp h2
  have hsτ : 1 < (s + (τ : ℂ) * I).re := by
    have : (s + (τ : ℂ) * I).re = s.re := by simp
    rw [this]
    linarith
  have hs1 : 1 < s.re := by linarith
  have hsum1 := hasSum_zetaTerm hsτ
  have hsum2 := hasSum_zetaTerm hs1
  have hdiff := hsum1.sub hsum2
  have hterm : ∀ n, zetaTerm (s + (τ : ℂ) * I) n - zetaTerm s n =
      zetaTerm s n * (phase τ (n + 1) - 1) := by
    intro n
    have hcast : (((n : ℝ) + 1 : ℝ) : ℂ) = (((n + 1 : ℕ) : ℝ) : ℂ) := by push_cast; rfl
    rw [zetaTerm, zetaTerm, hcast, cpow_translate (by omega : 1 ≤ n + 1)]
    ring
  have hnorm : ∀ n, ‖zetaTerm s n‖ ≤ g n := by
    intro n
    rw [norm_zetaTerm]
    exact Real.rpow_le_rpow_of_exponent_le (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
      (by linarith)
  have hphase2 : ∀ n, ‖phase τ (n + 1) - 1‖ ≤ 2 := by
    intro n
    calc _ ≤ ‖phase τ (n + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_phase τ (by omega), norm_one]; norm_num
  have hbd : ∀ n, ‖zetaTerm (s + (τ : ℂ) * I) n - zetaTerm s n‖ ≤ g n * 2 := by
    intro n
    rw [hterm, norm_mul]
    exact mul_le_mul (hnorm n) (hphase2 n) (norm_nonneg _) (hg0 n)
  have hsm : Summable fun n => ‖zetaTerm (s + (τ : ℂ) * I) n - zetaTerm s n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbd (hgs.mul_right 2)
  have hsplit := hsm.sum_add_tsum_nat_add N
  have hhead : ∑ n ∈ Finset.range N, ‖zetaTerm (s + (τ : ℂ) * I) n - zetaTerm s n‖ ≤ A * δ := by
    rw [hA, Finset.sum_mul]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [hterm, norm_mul]
    have hpn : ‖phase τ (n + 1) - 1‖ ≤ (ArithmeticFunction.cardFactors (n + 1) : ℝ) * δ := by
      refine norm_phase_sub_one_le (by omega) fun p hp hd => hprime p ?_
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hp⟩
      have hle := Nat.le_of_dvd (by omega) hd
      have := Finset.mem_range.mp hn
      omega
    calc _ ≤ g n * ((ArithmeticFunction.cardFactors (n + 1) : ℝ) * δ) :=
          mul_le_mul (hnorm n) hpn (norm_nonneg _) (hg0 n)
      _ = _ := by ring
  have hrest : ∑' k, ‖zetaTerm (s + (τ : ℂ) * I) (k + N) - zetaTerm s (k + N)‖ ≤
      ∑' k, g (k + N) * 2 := by
    refine Summable.tsum_le_tsum (fun k => hbd (k + N)) ((summable_nat_add_iff N).mpr hsm) ?_
    exact ((summable_nat_add_iff N).mpr hgs).mul_right 2
  rw [tsum_mul_right] at hrest
  have hfinal : ‖riemannZeta (s + (τ : ℂ) * I) - riemannZeta s‖ ≤
      ∑' n, ‖zetaTerm (s + (τ : ℂ) * I) n - zetaTerm s n‖ := by
    rw [← hdiff.tsum_eq]
    exact norm_tsum_le_tsum_norm hsm
  have hNlt : ∑' k, g (k + N) < ε / 8 := hN
  linarith

end GaloisForLFunctions.RigidArithmeticOfCuts
