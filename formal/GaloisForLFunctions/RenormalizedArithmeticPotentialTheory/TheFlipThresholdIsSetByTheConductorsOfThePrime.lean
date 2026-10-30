import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.EveryFiniteFlipSetHasAnExactResolutionThreshold
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheTiltedSplineHasAPolynomialConductorFloor

/-!
# The flip threshold is set by the conductors of the prime

Split a Ramanujan packet `y = u + v` into its conductors prime to `p` (`u`) and divisible by `p`
(`v`). Dilation by `p^k` fixes `u`, and `u ⊥ v` in the period mean, so the flip at `p` meets `u`
only through `v`:

`2 Σ_k d(k) k^{-1/2} M(y·y(k·)) ≥ −κ_p (‖u‖‖v‖ + ‖v‖²)`, `κ_p = 4 log p · √p/(p − 1)`

(`twistLimitEnergy_primeFlip_ge`), by Cauchy–Schwarz and `M(v(k·)²) ≤ k M(v²)`. The conductors
of `v` are expensive: by Möbius inversion `E_{pm}(c) ≥ E_m(c/p) ≥ E(c/p)`
(`completedConductorEnergy_prime_mul_ge`), the pole energy at the overlap `c/p`, which is
`log(p/(2πc)) + O(1)` for `c ≤ p`. A two-by-two minimization then gives

`λ_p(c) ≥ E(c) − κ_p²/(4 (E(c/p) − κ_p − E(c)))`  (`resolutionBottom_primeFlip_ge`),

and above the threshold `4 E(c) (E(c/p) − κ_p − E(c)) ≤ κ_p²`
(`margin_mul_le_of_primeFlip_resolutionThreshold_lt`): the margin at resolution is of order
`log² p/(p log(p/c))`, the squared coupling of the pole to the `p`-conductors over their energy.
For the tilted spline, `E(c) ≥ C₀ c⁻⁷` turns this into `c_0(ω_p)⁷ ≳ p/log p`
(`tiltedUnitSpline_primeFlip_resolutionThreshold_sharp_lower`), the order of the corpus upper
bound `(Kp)^{1/7}` up to the logarithm.
-/

noncomputable section

open MeasureTheory Filter Topology Finset Matrix
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticLorentzianGeometry
  RenormalizedBiarithmeticGeometry CompletedShell ArithmeticCastelnuovoSeveri Zeta23
  ArithmeticCountingPositivity TransMetzlerWeilPositivity.BoundedOverlap BezoutValuationIncidence
open _root_.RHTower (vonMangoldtAtom)

/-! ### Period means -/

/-- Cauchy–Schwarz for period means. -/
theorem periodMean_mul_sq_le (f g : ℕ → ℝ) (P : ℕ) :
    periodMean (fun a => f a * g a) P ^ 2 ≤
      periodMean (fun a => f a ^ 2) P * periodMean (fun a => g a ^ 2) P := by
  unfold periodMean
  rw [div_pow, div_mul_div_comm, ← sq]
  exact div_le_div_of_nonneg_right (sum_mul_sq_le_sq_mul_sq (range P) f g) (sq_nonneg _)

theorem sum_range_mul_of_periodic {g : ℕ → ℝ} {P : ℕ} (hg : Function.Periodic g P) (k : ℕ) :
    ∑ b ∈ range (k * P), g b = k * ∑ b ∈ range P, g b := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, sum_range_add, ih]
    have : ∑ x ∈ range P, g (k * P + x) = ∑ x ∈ range P, g x := by
      refine sum_congr rfl fun x _ => ?_
      rw [add_comm]
      simpa only [Nat.cast_id] using (hg.nat_mul k) x
    rw [this]
    push_cast
    ring

/-- **Dilation costs at most its factor**: `M(v(k·)²) ≤ k M(v²)`. -/
theorem periodMean_dilate_sq_le {v : ℕ → ℝ} {P : ℕ} (hP : 0 < P) (hv : Function.Periodic v P)
    {k : ℕ} (hk : 0 < k) :
    periodMean (fun a => v (k * a) ^ 2) P ≤ k * periodMean (fun a => v a ^ 2) P := by
  unfold periodMean
  rw [mul_div_assoc']
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  have hinj : Set.InjOn (fun a => k * a) (range P) := fun a _ b _ h =>
    Nat.eq_of_mul_eq_mul_left hk h
  have himg : (range P).image (fun a => k * a) ⊆ range (k * P) := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
    exact mem_range.mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp ha) hk)
  calc ∑ a ∈ range P, v (k * a) ^ 2 = ∑ b ∈ (range P).image (fun a => k * a), v b ^ 2 :=
        (sum_image (f := fun b => v b ^ 2) hinj).symm
    _ ≤ ∑ b ∈ range (k * P), v b ^ 2 :=
        sum_le_sum_of_subset_of_nonneg himg fun b _ _ => sq_nonneg _
    _ = k * ∑ b ∈ range P, v b ^ 2 :=
        sum_range_mul_of_periodic (g := fun b => v b ^ 2) (fun b => by
          show v (b + P) ^ 2 = v b ^ 2
          rw [hv b]) k

/-! ### Splitting a packet at a prime -/

/-- Ramanujan modes of conductor prime to `q` do not see dilation by `q`. -/
theorem normalizedRamanujanMode_coprime_mul {l q : ℕ} (hl : 0 < l) (hq : Nat.Coprime q l)
    (n : ℕ) : normalizedRamanujanMode l (q * n) = normalizedRamanujanMode l n := by
  rw [normalizedRamanujanMode_eq_coefficient hl, normalizedRamanujanMode_eq_coefficient hl]
  congr 1
  unfold ramanujanLagCoefficient
  refine sum_congr rfl fun d hd => ?_
  have hcop : Nat.Coprime d q := (hq.coprime_dvd_right (Nat.dvd_of_mem_divisors hd)).symm
  simp only [hcop.dvd_mul_left]

/-- The part of a packet on conductors prime to `p`. -/
def coprimePart (p : ℕ) (T : Finset ℕ) (β : ℕ → ℝ) : ℕ → ℝ := packetProfile (T.filter (¬ p ∣ ·)) β

/-- The part of a packet on conductors divisible by `p`. -/
def divisiblePart (p : ℕ) (T : Finset ℕ) (β : ℕ → ℝ) : ℕ → ℝ := packetProfile (T.filter (p ∣ ·)) β

theorem packetProfile_eq_parts (p : ℕ) (T : Finset ℕ) (β : ℕ → ℝ) (n : ℕ) :
    packetProfile T β n = coprimePart p T β n + divisiblePart p T β n := by
  unfold coprimePart divisiblePart packetProfile
  rw [add_comm, sum_filter_add_sum_filter_not]

theorem coprimePart_dilate {p : ℕ} (hp : p.Prime) {T : Finset ℕ} (hT : ∀ m ∈ T, 0 < m)
    (β : ℕ → ℝ) (k n : ℕ) : coprimePart p T β (p ^ k * n) = coprimePart p T β n := by
  unfold coprimePart packetProfile
  refine sum_congr rfl fun m hm => ?_
  obtain ⟨hmT, hpm⟩ := mem_filter.mp hm
  rw [normalizedRamanujanMode_coprime_mul (hT m hmT)
    (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm))]

/-- Period means of products of subpackets: `M(y_{S₁} y_{S₂}) = Σ_{m ∈ S₁ ∩ S₂} β_m²`. -/
theorem periodMean_packet_mul {T S₁ S₂ : Finset ℕ} (hT : ∀ m ∈ T, 0 < m) (h₁ : S₁ ⊆ T)
    (h₂ : S₂ ⊆ T) (β : ℕ → ℝ) :
    periodMean (fun a => packetProfile S₁ β a * packetProfile S₂ β a) (packetPeriod T) =
      ∑ m ∈ S₁.filter (· ∈ S₂), β m ^ 2 := by
  have hP := packetPeriod_pos hT
  have hdiv : ∀ m ∈ T, m ∣ packetPeriod T := fun m hm => Finset.dvd_prod_of_mem _ hm
  have hlin : periodMean (fun a => packetProfile S₁ β a * packetProfile S₂ β a) (packetPeriod T) =
      ∑ m ∈ S₁, ∑ l ∈ S₂, β m * β l * periodMean
        (fun a => normalizedRamanujanMode m a * normalizedRamanujanMode l a) (packetPeriod T) := by
    unfold periodMean packetProfile
    rw [Finset.sum_congr rfl fun a _ => sum_mul_sum S₁ S₂ _ _, Finset.sum_comm, sum_div]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_comm, sum_div]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_div_assoc', mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hlin]
  have hterm : ∀ m ∈ S₁, ∑ l ∈ S₂, β m * β l * periodMean
      (fun a => normalizedRamanujanMode m a * normalizedRamanujanMode l a) (packetPeriod T) =
      if m ∈ S₂ then β m ^ 2 else 0 := by
    intro m hm
    have hmT := h₁ hm
    have hinner : ∀ l ∈ S₂, β m * β l * periodMean
        (fun a => normalizedRamanujanMode m a * normalizedRamanujanMode l a) (packetPeriod T) =
        β m * β l * (if m = l then 1 else 0) := fun l hl => by
      rw [periodMean_normalizedRamanujanMode_mul (hT m hmT) (hT l (h₂ hl)) (hdiv m hmT)
        (hdiv l (h₂ hl)) hP]
    rw [Finset.sum_congr (rfl : S₂ = S₂) hinner]
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq]
    split_ifs <;> ring
  calc ∑ m ∈ S₁, ∑ l ∈ S₂, β m * β l * periodMean
        (fun a => normalizedRamanujanMode m a * normalizedRamanujanMode l a) (packetPeriod T) =
      ∑ m ∈ S₁, (if m ∈ S₂ then β m ^ 2 else 0) := Finset.sum_congr rfl hterm
    _ = ∑ m ∈ S₁.filter (· ∈ S₂), β m ^ 2 := by rw [sum_filter]

/-! ### The flip energy against the `p`-conductors -/

/-- The flip coupling `κ_p = 4 log p · √p/(p − 1)`. -/
def flipCoupling (p : ℕ) : ℝ := 4 * Real.log p * Real.sqrt p / ((p : ℝ) - 1)

/-- One lag of the flip sees `u` only through `v`:
`M(y·y(p^k·)) ≥ −p^{k/2} (√α √β + β)` with `α = Σ_{p∤m} β_m²`, `β = Σ_{p∣m} β_m²`. -/
theorem shiftMean_primePow_ge {p : ℕ} (hp : p.Prime) {T : Finset ℕ} (hT : ∀ m ∈ T, 0 < m)
    (β : ℕ → ℝ) (k : ℕ) :
    -(Real.sqrt p ^ k * (Real.sqrt (∑ m ∈ T.filter (¬ p ∣ ·), β m ^ 2) *
        Real.sqrt (∑ m ∈ T.filter (p ∣ ·), β m ^ 2) + ∑ m ∈ T.filter (p ∣ ·), β m ^ 2)) ≤
      shiftMean (packetProfile T β) (packetPeriod T) (p ^ k) := by
  have hP := packetPeriod_pos hT
  obtain ⟨α, hα⟩ : ∃ α, α = ∑ m ∈ T.filter (¬ p ∣ ·), β m ^ 2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = ∑ m ∈ T.filter (p ∣ ·), β m ^ 2 := ⟨_, rfl⟩
  rw [← hα, ← hb]
  have hα0 : 0 ≤ α := by rw [hα]; exact sum_nonneg fun m _ => sq_nonneg _
  have hb0 : 0 ≤ b := by rw [hb]; exact sum_nonneg fun m _ => sq_nonneg _
  have hT0 : T.filter (¬ p ∣ ·) ⊆ T := filter_subset _ _
  have hT1 : T.filter (p ∣ ·) ⊆ T := filter_subset _ _
  -- the means of the parts
  have huu : periodMean (fun a => coprimePart p T β a ^ 2) (packetPeriod T) = α := by
    have h := periodMean_packet_mul hT hT0 hT0 β
    rw [filter_true_of_mem (fun m hm => hm), ← hα] at h
    rw [← h]
    congr 1
    funext a
    rw [sq]
    rfl
  have hvv : periodMean (fun a => divisiblePart p T β a ^ 2) (packetPeriod T) = b := by
    have h := periodMean_packet_mul hT hT1 hT1 β
    rw [filter_true_of_mem (fun m hm => hm), ← hb] at h
    rw [← h]
    congr 1
    funext a
    rw [sq]
    rfl
  have hvu : periodMean (fun a => divisiblePart p T β a * coprimePart p T β a)
      (packetPeriod T) = 0 := by
    have h := periodMean_packet_mul hT hT1 hT0 β
    rw [filter_false_of_mem (fun m (hm : m ∈ T.filter (p ∣ ·))
        (hm' : m ∈ T.filter (¬ p ∣ ·)) => (mem_filter.mp hm').2 (mem_filter.mp hm).2),
      sum_empty] at h
    exact h
  -- `v` is periodic, so its dilation costs at most `p^k`
  have hvper : Function.Periodic (divisiblePart p T β) (packetPeriod T) := by
    intro n
    unfold divisiblePart packetProfile
    refine sum_congr rfl fun m hm => ?_
    obtain ⟨q, hq⟩ : m ∣ packetPeriod T := Finset.dvd_prod_of_mem _ (hT1 hm)
    rw [hq]
    congr 1
    simpa only [Nat.cast_id, Nat.mul_comm] using
      ((normalizedRamanujanMode_periodic (hT m (hT1 hm))).nat_mul q) n
  have hdil := periodMean_dilate_sq_le hP hvper (pow_pos hp.pos k)
  rw [hvv] at hdil
  -- the expansion `y·y(p^k·) = u² + u·v(p^k·) + v·u + v·v(p^k·)`
  have hexp : shiftMean (packetProfile T β) (packetPeriod T) (p ^ k) =
      α + periodMean (fun a => coprimePart p T β a * divisiblePart p T β (p ^ k * a))
        (packetPeriod T) +
      periodMean (fun a => divisiblePart p T β a * coprimePart p T β a) (packetPeriod T) +
      periodMean (fun a => divisiblePart p T β a * divisiblePart p T β (p ^ k * a))
        (packetPeriod T) := by
    have hfun : (fun a => packetProfile T β a * packetProfile T β (p ^ k * a)) =
        fun a => coprimePart p T β a ^ 2 + coprimePart p T β a * divisiblePart p T β (p ^ k * a) +
          divisiblePart p T β a * coprimePart p T β a +
          divisiblePart p T β a * divisiblePart p T β (p ^ k * a) := by
      funext a
      rw [packetProfile_eq_parts p T β a, packetProfile_eq_parts p T β (p ^ k * a),
        coprimePart_dilate hp hT β k a]
      ring
    unfold shiftMean
    rw [hfun, ← huu]
    unfold periodMean
    simp only [sum_add_distrib, add_div]
  have hcs1 := periodMean_mul_sq_le (coprimePart p T β)
    (fun a => divisiblePart p T β (p ^ k * a)) (packetPeriod T)
  have hcs2 := periodMean_mul_sq_le (divisiblePart p T β)
    (fun a => divisiblePart p T β (p ^ k * a)) (packetPeriod T)
  rw [huu] at hcs1
  rw [hvv] at hcs2
  have hpk : (0 : ℝ) ≤ ((p ^ k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsq : Real.sqrt p ^ k = Real.sqrt ((p ^ k : ℕ) : ℝ) := by
    rw [Nat.cast_pow, sqrt_natCast_pow]
  have h1 : |periodMean (fun a => coprimePart p T β a * divisiblePart p T β (p ^ k * a))
      (packetPeriod T)| ≤ Real.sqrt p ^ k * (Real.sqrt α * Real.sqrt b) := by
    rw [hsq, ← Real.sqrt_mul hα0, ← Real.sqrt_mul hpk]
    refine Real.abs_le_sqrt (hcs1.trans ?_)
    calc α * periodMean (fun a => divisiblePart p T β (p ^ k * a) ^ 2) (packetPeriod T)
        ≤ α * (((p ^ k : ℕ) : ℝ) * b) := mul_le_mul_of_nonneg_left hdil hα0
      _ = ((p ^ k : ℕ) : ℝ) * (α * b) := by ring
  have h2 : |periodMean (fun a => divisiblePart p T β a * divisiblePart p T β (p ^ k * a))
      (packetPeriod T)| ≤ Real.sqrt p ^ k * b := by
    rw [hsq, ← Real.sqrt_sq hb0, ← Real.sqrt_mul hpk]
    refine Real.abs_le_sqrt (hcs2.trans ?_)
    calc b * periodMean (fun a => divisiblePart p T β (p ^ k * a) ^ 2) (packetPeriod T)
        ≤ b * (((p ^ k : ℕ) : ℝ) * b) := mul_le_mul_of_nonneg_left hdil hb0
      _ = ((p ^ k : ℕ) : ℝ) * b ^ 2 := by ring
  rw [hexp, hvu]
  have := (abs_le.mp h1).1
  have := (abs_le.mp h2).1
  nlinarith

theorem flipCoupling_eq_tsum {p : ℕ} (hp : p.Prime) :
    4 * Real.log p * ∑' j : ℕ, (Real.sqrt p)⁻¹ ^ (2 * j + 1) = flipCoupling p := by
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hss : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt (Nat.cast_nonneg p)
  have hr2 : ((Real.sqrt p)⁻¹) ^ 2 = 1 / (p : ℝ) := by
    rw [inv_pow, sq, hss, one_div]
  have hr2lt : ((Real.sqrt p)⁻¹) ^ 2 < 1 := by
    rw [hr2, div_lt_one (by linarith)]; exact hp1
  have hgeo := tsum_geometric_of_lt_one (by positivity) hr2lt
  have hsum : ∑' j : ℕ, (Real.sqrt p)⁻¹ ^ (2 * j + 1) =
      (Real.sqrt p)⁻¹ * ∑' j : ℕ, (((Real.sqrt p)⁻¹) ^ 2) ^ j := by
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by ring
  have key : (Real.sqrt p)⁻¹ * (1 - 1 / (p : ℝ))⁻¹ = Real.sqrt p / ((p : ℝ) - 1) := by
    have hp0 : (p : ℝ) - 1 ≠ 0 := by linarith
    have hpne : (p : ℝ) ≠ 0 := by linarith
    rw [show (1 : ℝ) - 1 / p = ((p : ℝ) - 1) / p by field_simp, inv_div,
      show (Real.sqrt p)⁻¹ * ((p : ℝ) / ((p : ℝ) - 1)) = ((p : ℝ) / Real.sqrt p) / ((p : ℝ) - 1) by
        ring, Real.div_sqrt]
  rw [hsum, hgeo, hr2, key, flipCoupling]
  ring

/-- **The flip meets the `p`-conductors only.** For a packet with mass `α` on conductors prime to
`p` and `b` on conductors divisible by `p`, the flip energy is at least `−κ_p(√α √b + b)`. -/
theorem twistLimitEnergy_primeFlip_ge {p : ℕ} (hp : p.Prime) {T : Finset ℕ}
    (hT : ∀ m ∈ T, 0 < m) (β : ℕ → ℝ) :
    -(flipCoupling p * (Real.sqrt (∑ m ∈ T.filter (¬ p ∣ ·), β m ^ 2) *
        Real.sqrt (∑ m ∈ T.filter (p ∣ ·), β m ^ 2) + ∑ m ∈ T.filter (p ∣ ·), β m ^ 2)) ≤
      twistLimitEnergy (primeFlipWeight p) (packetProfile T β) (packetPeriod T) := by
  set C := Real.sqrt (∑ m ∈ T.filter (¬ p ∣ ·), β m ^ 2) *
    Real.sqrt (∑ m ∈ T.filter (p ∣ ·), β m ^ 2) + ∑ m ∈ T.filter (p ∣ ·), β m ^ 2 with hC
  have hP := packetPeriod_pos hT
  have hper := packetProfile_periodic hT β
  rw [twistLimitEnergy_primeFlip hp hP hper]
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hss : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt (Nat.cast_nonneg p)
  have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  -- the geometric comparison series
  have hr : (Real.sqrt p)⁻¹ < 1 := by
    rw [inv_lt_one₀ hsp, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one hp1
  have hgeom : Summable fun j : ℕ => (Real.sqrt p)⁻¹ ^ (2 * j + 1) :=
    (summable_geometric_of_lt_one (by positivity) hr).comp_injective
      (i := fun j : ℕ => 2 * j + 1) (fun a b (h : 2 * a + 1 = 2 * b + 1) => by omega)
  -- the actual series is summable: its means are bounded
  set B := (∑ i ∈ range (packetPeriod T), |packetProfile T β i|) ^ 2
  have hM := abs_shiftMean_le hP hper
  have hsum : Summable fun j : ℕ =>
      shiftMean (packetProfile T β) (packetPeriod T) (p ^ (2 * j + 1)) / (p : ℝ) ^ (2 * j + 1) := by
    refine Summable.of_norm_bounded (hgeom.mul_left B) fun j => ?_
    have hpj : (0 : ℝ) < (p : ℝ) ^ (2 * j + 1) := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpj]
    have hpow : (p : ℝ) ^ (2 * j + 1) = (Real.sqrt p) ^ (2 * j + 1) * Real.sqrt p ^ (2 * j + 1) := by
      rw [← mul_pow, hss]
    have hsn : 1 ≤ Real.sqrt p ^ (2 * j + 1) := one_le_pow₀ (by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hp1.le)
    have hB : 0 ≤ B := sq_nonneg _
    calc |shiftMean (packetProfile T β) (packetPeriod T) (p ^ (2 * j + 1))| / (p : ℝ) ^ (2 * j + 1)
        ≤ B / (p : ℝ) ^ (2 * j + 1) := div_le_div_of_nonneg_right (hM _) hpj.le
      _ = B / (Real.sqrt p ^ (2 * j + 1) * Real.sqrt p ^ (2 * j + 1)) := by rw [hpow]
      _ ≤ B / Real.sqrt p ^ (2 * j + 1) :=
          div_le_div_of_nonneg_left hB (by positivity) (le_mul_of_one_le_right (by positivity) hsn)
      _ = B * (Real.sqrt p)⁻¹ ^ (2 * j + 1) := by rw [inv_pow, div_eq_mul_inv]
  -- termwise comparison
  have hterm : ∀ j : ℕ, -(C * (Real.sqrt p)⁻¹ ^ (2 * j + 1)) ≤
      shiftMean (packetProfile T β) (packetPeriod T) (p ^ (2 * j + 1)) / (p : ℝ) ^ (2 * j + 1) := by
    intro j
    have h := shiftMean_primePow_ge hp hT β (2 * j + 1)
    rw [← hC] at h
    have hpj : (0 : ℝ) < (p : ℝ) ^ (2 * j + 1) := by positivity
    rw [le_div_iff₀ hpj]
    have hpow : (p : ℝ) ^ (2 * j + 1) = (Real.sqrt p) ^ (2 * j + 1) * Real.sqrt p ^ (2 * j + 1) := by
      rw [← mul_pow, hss]
    have hne : Real.sqrt p ^ (2 * j + 1) ≠ 0 := by positivity
    have : -(C * (Real.sqrt p)⁻¹ ^ (2 * j + 1)) * (p : ℝ) ^ (2 * j + 1) =
        -(Real.sqrt p ^ (2 * j + 1) * C) := by
      rw [hpow, inv_pow]
      field_simp
    rw [this]
    linarith
  have hle := Summable.tsum_le_tsum hterm (hgeom.mul_left C).neg hsum
  rw [tsum_neg, tsum_mul_left] at hle
  have hκ := flipCoupling_eq_tsum hp
  have := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 4 * Real.log p)
  rw [← hκ]
  linarith

/-! ### The conductors of `p` are expensive -/

section Conductors

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
  (hM : 0 < ∫ u, φ u ^ 2)
include hφ hsupp hM

/-- **Möbius inversion at a prime**: `E_{pm}(c) ≥ E_m(c/p)`. For `p ∣ m` this is an identity; for
`p ∤ m`, `E_{pm}(c) = (p E_m(c/p) − E_m(c))/(p − 1)` and `E_m` decreases in the overlap. -/
theorem completedConductorEnergy_prime_mul_ge {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : 0 < m)
    {c : ℝ} (hc : 0 < c) :
    completedConductorEnergy φ (c / p) m ≤ completedConductorEnergy φ c (p * m) := by
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hpm : 0 < p * m := Nat.mul_pos hp0 hm
  set F : ℕ → ℝ := fun d =>
    (ArithmeticFunction.moebius (p * m / d) : ℝ) * d * completedShellEnergy φ (c / d) with hF
  set S := ∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m / d) : ℝ) * d *
    completedShellEnergy φ (c / p / d) with hS
  set S₀ := ∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m / d) : ℝ) * d *
    completedShellEnergy φ (c / d) with hS₀
  have htotm : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hEm : completedConductorEnergy φ (c / p) m = S / m.totient := rfl
  have hEm₀ : completedConductorEnergy φ c m = S₀ / m.totient := rfl
  -- the divisors of `pm` divisible by `p` are `p · (divisors of m)`
  have hdiv : ∑ d ∈ (p * m).divisors.filter (p ∣ ·), F d = p * S := by
    rw [hS, mul_sum]
    refine Finset.sum_nbij' (fun d => d / p) (fun d => p * d) ?_ ?_ ?_ ?_ ?_
    · intro d hd
      obtain ⟨hd1, hpd⟩ := mem_filter.mp hd
      obtain ⟨e, rfl⟩ := hpd
      rw [Nat.mul_div_cancel_left e hp0]
      exact Nat.mem_divisors.mpr ⟨(Nat.mul_dvd_mul_iff_left hp0).mp
        (Nat.dvd_of_mem_divisors hd1), hm.ne'⟩
    · intro d hd
      refine mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_left p
        (Nat.dvd_of_mem_divisors hd), hpm.ne'⟩, dvd_mul_right p d⟩
    · intro d hd
      obtain ⟨e, rfl⟩ := (mem_filter.mp hd).2
      rw [Nat.mul_div_cancel_left e hp0]
    · intro d _
      exact Nat.mul_div_cancel_left d hp0
    · intro d hd
      obtain ⟨e, rfl⟩ := (mem_filter.mp hd).2
      simp only [hF, Nat.mul_div_cancel_left e hp0, Nat.mul_div_mul_left m e hp0, Nat.cast_mul,
        div_div]
      ring
  have hsplit := (sum_filter_add_sum_filter_not (p * m).divisors (p ∣ ·) F).symm
  have hEpm : completedConductorEnergy φ c (p * m) = (∑ d ∈ (p * m).divisors, F d) /
      (p * m).totient := rfl
  have hEanti : completedConductorEnergy φ c m ≤ completedConductorEnergy φ (c / p) m :=
    completedConductorEnergy_anti hφ hsupp hM (div_pos hc hpR)
      (div_le_self hc.le (by exact_mod_cast hp.one_lt.le)) hm
  by_cases hpdm : p ∣ m
  · -- the coprime part vanishes: `p² ∣ pm/d`
    have hzero : ∑ d ∈ (p * m).divisors.filter (¬ p ∣ ·), F d = 0 := by
      refine sum_eq_zero fun d hd => ?_
      obtain ⟨hd1, hpd⟩ := mem_filter.mp hd
      have hdpm := Nat.dvd_of_mem_divisors hd1
      have hcop : Nat.Coprime d p := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd))
      have hdm : d ∣ m := hcop.dvd_of_dvd_mul_left hdpm
      obtain ⟨m₁, rfl⟩ := hpdm
      have hdm₁ : d ∣ m₁ := hcop.dvd_of_dvd_mul_left hdm
      obtain ⟨e, he⟩ := hdm₁
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd1
      have hq : p * (p * m₁) / d = p * p * e := by
        rw [he, show p * (p * (d * e)) = d * (p * p * e) by ring]
        exact Nat.mul_div_cancel_left _ hd0
      have hnsq : ¬ Squarefree (p * p * e) := fun h =>
        (Nat.Prime.one_lt hp).ne' (Nat.isUnit_iff.mp (h p (dvd_mul_right _ _)))
      simp only [hF, hq, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq, Int.cast_zero,
        zero_mul]
    rw [hEpm, hsplit, hdiv, hzero, add_zero, Nat.totient_mul_of_prime_of_dvd hp hpdm, Nat.cast_mul,
      hEm]
    rw [mul_div_mul_left _ _ hpR.ne']
  · -- `p ∤ m`: the coprime divisors are those of `m`, with Möbius sign `−1`
    have hcop : ∑ d ∈ (p * m).divisors.filter (¬ p ∣ ·), F d = -S₀ := by
      have hset : (p * m).divisors.filter (¬ p ∣ ·) = m.divisors := by
        ext d
        simp only [mem_filter, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨hd, -⟩, hpd⟩
          exact ⟨(Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd)).dvd_of_dvd_mul_left
            hd, hm.ne'⟩
        · rintro ⟨hd, -⟩
          exact ⟨⟨dvd_mul_of_dvd_right hd p, hpm.ne'⟩, fun h => hpdm (h.trans hd)⟩
      rw [hset, hS₀, ← sum_neg_distrib]
      refine sum_congr rfl fun d hd => ?_
      have hdm := Nat.dvd_of_mem_divisors hd
      have hq : p * m / d = p * (m / d) := Nat.mul_div_assoc p hdm
      have hcopm : Nat.Coprime p (m / d) :=
        (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hpdm (h.trans (Nat.div_dvd_of_dvd hdm))
      simp only [hF, hq, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcopm,
        ArithmeticFunction.moebius_apply_prime hp]
      push_cast
      ring
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    rw [hEpm, hsplit, hdiv, hcop, Nat.totient_mul_of_prime_of_not_dvd hp hpdm, Nat.cast_mul,
      Nat.cast_sub hp.one_le, Nat.cast_one]
    rw [hEm] at hEanti ⊢
    rw [hEm₀] at hEanti
    rw [div_le_div_iff₀ htotm (mul_pos (by linarith) htotm)]
    rw [div_le_div_iff₀ htotm htotm] at hEanti
    nlinarith

/-- Every conductor divisible by `p` costs at least the pole energy at overlap `c/p`. -/
theorem completedShellEnergy_div_le_of_dvd {p : ℕ} (hp : p.Prime) {l : ℕ} (hl : 0 < l)
    (hpl : p ∣ l) {c : ℝ} (hc : 0 < c) :
    completedShellEnergy φ (c / p) ≤ completedConductorEnergy φ c l := by
  obtain ⟨m, rfl⟩ := hpl
  have hm : 0 < m := Nat.pos_of_mul_pos_left hl
  have hcp : 0 < c / p := div_pos hc (by exact_mod_cast hp.pos)
  calc completedShellEnergy φ (c / p) = completedConductorEnergy φ (c / p) 1 :=
        (completedConductorEnergy_one φ (c / p)).symm
    _ ≤ completedConductorEnergy φ (c / p) m := completedConductorEnergy_one_le hφ hsupp hM hcp hm
    _ ≤ completedConductorEnergy φ c (p * m) :=
        completedConductorEnergy_prime_mul_ge hφ hsupp hM hp hm hc

/-- **The bottom of a flip.** When the `p`-conductors exceed the pole by more than the coupling,
`λ_p(c) ≥ E(c) − κ_p²/(4 D)`, `D = E(c/p) − κ_p − E(c)`. -/
theorem resolutionBottom_primeFlip_ge {p : ℕ} (hp : p.Prime) {c : ℝ} (hc : 0 < c)
    (hD : 0 < completedShellEnergy φ (c / p) - flipCoupling p - completedShellEnergy φ c) :
    completedShellEnergy φ c - flipCoupling p ^ 2 /
        (4 * (completedShellEnergy φ (c / p) - flipCoupling p - completedShellEnergy φ c)) ≤
      resolutionBottom (primeFlipWeight p) φ c := by
  set E := completedShellEnergy φ c with hE
  set E' := completedShellEnergy φ (c / p) with hE'
  set κ := flipCoupling p with hκ
  set D := E' - κ - E with hDdef
  refine le_resolutionBottom fun T hT β hβ => ?_
  set α := ∑ m ∈ T.filter (¬ p ∣ ·), β m ^ 2 with hα
  set b := ∑ m ∈ T.filter (p ∣ ·), β m ^ 2 with hb
  have hα0 : 0 ≤ α := sum_nonneg fun m _ => sq_nonneg _
  have hb0 : 0 ≤ b := sum_nonneg fun m _ => sq_nonneg _
  have hab : α + b = 1 := by
    rw [hα, hb, ← hβ, add_comm]
    exact sum_filter_add_sum_filter_not T (p ∣ ·) (fun m => β m ^ 2)
  -- conductor energies
  have hlow : E * α + E' * b ≤ ∑ m ∈ T, β m ^ 2 * completedConductorEnergy φ c m := by
    rw [← sum_filter_add_sum_filter_not T (p ∣ ·) (fun m => β m ^ 2 * completedConductorEnergy φ c m),
      hα, hb, mul_sum, mul_sum, add_comm]
    refine add_le_add (sum_le_sum fun m hm => ?_) (sum_le_sum fun m hm => ?_)
    · obtain ⟨hmT, hpm⟩ := mem_filter.mp hm
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left
        (completedShellEnergy_div_le_of_dvd hφ hsupp hM hp (hT m hmT) hpm hc) (sq_nonneg _)
    · obtain ⟨hmT, -⟩ := mem_filter.mp hm
      rw [mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      rw [hE, ← completedConductorEnergy_one]
      exact completedConductorEnergy_one_le hφ hsupp hM hc (hT m hmT)
  have htwist := twistLimitEnergy_primeFlip_ge hp hT β
  rw [← hα, ← hb, ← hκ] at htwist
  -- the two-by-two minimization
  set x := Real.sqrt α
  set y := Real.sqrt b
  have hxx : x ^ 2 = α := Real.sq_sqrt hα0
  have hyy : y ^ 2 = b := Real.sq_sqrt hb0
  have hx1 : x ^ 2 ≤ 1 := by rw [hxx]; linarith
  have hκ0 : 0 ≤ κ := by
    rw [hκ, flipCoupling]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have := Real.log_natCast_nonneg p
    have := Real.sqrt_nonneg (p : ℝ)
    exact div_nonneg (by positivity) (by linarith)
  have hamgm : κ * (x * y) ≤ D * y ^ 2 + κ ^ 2 / (4 * D) := by
    have hsq : 0 ≤ (2 * D * y - κ * x) ^ 2 := sq_nonneg _
    have h4D : 0 < 4 * D := by linarith
    rw [← sub_nonneg]
    have : D * y ^ 2 + κ ^ 2 / (4 * D) - κ * (x * y) =
        ((2 * D * y - κ * x) ^ 2 + κ ^ 2 * (1 - x ^ 2)) / (4 * D) := by
      field_simp
      ring
    rw [this]
    exact div_nonneg (add_nonneg hsq (mul_nonneg (sq_nonneg _) (by linarith))) h4D.le
  unfold packetEnergy
  have hfin : E - κ ^ 2 / (4 * D) ≤ E * α + E' * b - κ * (x * y + b) := by
    have h1 : E * α + E' * b - κ * (x * y + b) = E * (α + b) + D * b - κ * (x * y) := by
      rw [hDdef]; ring
    rw [h1, hab, mul_one, ← hyy]
    linarith
  linarith

end Conductors

/-! ### The margin at the threshold of a flip -/

/-- **The sharp resolution law of a flip.** Above the threshold `c_0(ω_p)`, whenever the
`p`-conductors exceed the pole by more than the coupling,
`4 E(c) (E(c/p) − κ_p − E(c)) ≤ κ_p²`. -/
theorem margin_mul_le_of_primeFlip_resolutionThreshold_lt {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hFT : ∀ r : ℝ, paperFT (cx φ) (r : ℂ) ≠ 0)
    {p : ℕ} (hp : p.Prime) {c : ℝ} (hlt : resolutionThreshold (primeFlipWeight p) φ < c)
    (hD : 0 < completedShellEnergy φ (c / p) - flipCoupling p - completedShellEnergy φ c) :
    4 * completedShellEnergy φ c *
        (completedShellEnergy φ (c / p) - flipCoupling p - completedShellEnergy φ c) ≤
      flipCoupling p ^ 2 := by
  have hM := integral_sq_pos_of_noRealZero hφ hsupp hFT
  obtain ⟨c₁, hc₁, hseen⟩ := exists_primeFlip_resolutionBottom_neg hφ hsupp hFT hp
  have hth := (resolutionThreshold_spec hφ hsupp hFT (summable_abs_twistDefect_primeFlip hp)
    hc₁ hseen).1
  have hc : 0 < c := hth.trans hlt
  -- above the threshold the bottom is not positive
  have hle : resolutionBottom (primeFlipWeight p) φ c ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    have hbdd : BddAbove {c : ℝ | 0 < c ∧ 0 < resolutionBottom (primeFlipWeight p) φ c} := by
      refine ⟨c₁, fun c' hc' => ?_⟩
      by_contra hlt'
      push_neg at hlt'
      have := resolutionBottom_antitone hφ hsupp hM (summable_abs_twistDefect_primeFlip hp) hc₁
        hlt'.le
      linarith [hc'.2]
    have : c ≤ resolutionThreshold (primeFlipWeight p) φ := le_csSup hbdd ⟨hc, hpos⟩
    linarith
  have hbot := resolutionBottom_primeFlip_ge hφ hsupp hM hp hc hD
  have h4D : 0 < 4 * (completedShellEnergy φ (c / p) - flipCoupling p - completedShellEnergy φ c) :=
    by linarith
  have h1 : completedShellEnergy φ c ≤ flipCoupling p ^ 2 /
      (4 * (completedShellEnergy φ (c / p) - flipCoupling p - completedShellEnergy φ c)) := by
    linarith
  rw [le_div_iff₀ h4D] at h1
  linarith

/-! ### The tilted spline: `c_0(ω_p)⁷ ≳ p/log p` -/

theorem flipCoupling_le {p : ℕ} (hp : p.Prime) :
    flipCoupling p ≤ 8 * Real.log p / Real.sqrt p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by linarith)
  have hss : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt (by linarith)
  have hlog := Real.log_natCast_nonneg p
  unfold flipCoupling
  rw [div_le_div_iff₀ (by linarith) hsp]
  nlinarith [mul_nonneg hlog hsp.le]

/-- The pole energy of the tilted spline at overlap `c/p ≤ 1` is at least
`log(p/(2πc)) + R`, `R` the spline's Robin constant. -/
theorem tiltedUnitSpline_completedShellEnergy_div_ge {p : ℕ} (hp : p.Prime) {c : ℝ}
    (hc : 0 < c) (hcp : c ≤ p) :
    Real.log (p / (2 * Real.pi * c)) + (bumpRobin tiltedUnitSpline 1 /
        (∫ u, tiltedUnitSpline u ^ 2) + ramanujanAdjunctionEnergy 1 -
          Real.eulerMascheroniConstant) ≤ completedShellEnergy tiltedUnitSpline (c / p) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hc0 : 0 < c / p := div_pos hc hpR
  have hc1 : c / p ≤ 1 := by rw [div_le_one hpR]; exact hcp
  rw [← completedConductorEnergy_one, completedConductorEnergy_eq_adjunction hc0 hc1 one_pos]
  unfold completeWeilAdjunctionEnergy completeWeilSelfFinitePart
  rw [if_pos rfl]
  have hpole := completeWeilPoleShift_nonneg tiltedUnitSpline hc0.le
  have hlog : Real.log (1 / (2 * Real.pi * (c / p))) = Real.log (p / (2 * Real.pi * c)) := by
    congr 1
    field_simp
  rw [hlog]
  linarith

/-- **The polynomial lower law of a flip threshold.** For the tilted unit spline there are
`κ > 0` and `p₀` such that every overlap `c` above `c_0(ω_p)`, `p ≥ p₀`, satisfies
`κ p ≤ log p · max(c, 1)⁷`; thus `c_0(ω_p) ≥ (κ p/log p)^{1/7}`, the sharp order up to the
logarithm. -/
theorem tiltedUnitSpline_primeFlip_resolutionThreshold_sharp_lower :
    ∃ κ : ℝ, 0 < κ ∧ ∃ p₀ : ℕ, ∀ p : ℕ, p.Prime → p₀ ≤ p → ∀ c : ℝ,
      resolutionThreshold (primeFlipWeight p) tiltedUnitSpline < c →
        κ * p ≤ Real.log p * max c 1 ^ 7 := by
  set C₀ := 2 * CriticalArithmeticCorrelationTheory.tiltedSplineTailConstant /
    (∫ u, tiltedUnitSpline u ^ 2) with hC₀
  have hC₀0 : 0 < C₀ := by
    have := CriticalArithmeticCorrelationTheory.tiltedSplineTailConstant_pos
    have := integral_tiltedUnitSpline_sq_pos
    positivity
  set R := bumpRobin tiltedUnitSpline 1 / (∫ u, tiltedUnitSpline u ^ 2) +
    ramanujanAdjunctionEnergy 1 - Real.eulerMascheroniConstant with hR
  set A := Real.log (2 * Real.pi) - R + 1 with hA
  -- large primes: `16 log p/√p ≤ 1` and `log p ≥ 4A`
  have hsmall := (tendsto_log_div_sqrt_natCast.const_mul 16).eventually
    (ge_mem_nhds (show 16 * 0 < (1 : ℝ) by norm_num))
  have hlarge := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (4 * A + 4))
  obtain ⟨p₁, hp₁⟩ := eventually_atTop.mp (hsmall.and hlarge)
  refine ⟨min (C₀ / 64) 1, lt_min (by positivity) one_pos, max p₁ 4, fun p hp hpp c hlt => ?_⟩
  obtain ⟨h16, hlogp⟩ := hp₁ p ((le_max_left _ _).trans hpp)
  have hlogA : 4 * A + 4 ≤ Real.log p := hlogp
  have hp4 : 4 ≤ p := (le_max_right _ _).trans hpp
  have hpR : (4 : ℝ) ≤ p := by exact_mod_cast hp4
  have hpR0 : (0 : ℝ) < p := by linarith
  have hlog1 : 1 ≤ Real.log p := by
    have h4 : 1 < Real.log 4 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith
    exact h4.le.trans (Real.log_le_log (by norm_num) hpR)
  have hlogp0 : 0 < Real.log p := by linarith
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hpR0
  have hss : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hpR0.le
  have hth := (primeFlip_resolutionThreshold_spec contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero paperFT_tiltedUnitSpline_real_ne_zero hp).1
  have hc : 0 < c := hth.trans hlt
  set m := max c 1 with hm
  have hm1 : 1 ≤ m := le_max_right c 1
  have hcm : c ≤ m := le_max_left c 1
  have hm7 : 1 ≤ m ^ 7 := one_le_pow₀ hm1
  have hκ1 : min (C₀ / 64) 1 ≤ 1 := min_le_right _ _
  have hκC : min (C₀ / 64) 1 ≤ C₀ / 64 := min_le_left _ _
  -- large overlaps are trivial
  by_cases hcbig : Real.sqrt p < c
  · have hm2 : p ≤ m ^ 2 := by
      have : Real.sqrt p < m := lt_of_lt_of_le hcbig hcm
      nlinarith
    have : (p : ℝ) ≤ m ^ 7 := by
      calc (p : ℝ) ≤ m ^ 2 := hm2
        _ ≤ m ^ 2 * m ^ 5 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hm1)
        _ = m ^ 7 := by ring
    calc min (C₀ / 64) 1 * p ≤ 1 * p := mul_le_mul_of_nonneg_right hκ1 hpR0.le
      _ ≤ Real.log p * m ^ 7 := by nlinarith
  push_neg at hcbig
  -- the margin is small above the threshold
  have hEsmall := completedShellEnergy_le_of_primeFlip_resolutionThreshold_lt
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero paperFT_tiltedUnitSpline_real_ne_zero hp hp4
    hlt
  have hκ := flipCoupling_le hp
  have h8 : 8 * Real.log p / Real.sqrt p ≤ 1 / 2 := by
    have : 16 * (Real.log p / Real.sqrt p) ≤ 1 := h16
    rw [mul_div_assoc]
    linarith
  -- the `p`-conductors are expensive: `D ≥ (log p)/4`
  have hcp : c ≤ p := hcbig.trans (by nlinarith)
  have hEp := tiltedUnitSpline_completedShellEnergy_div_ge hp hc hcp
  rw [← hR] at hEp
  have hlogdiv : Real.log p / 2 - Real.log (2 * Real.pi) ≤ Real.log (p / (2 * Real.pi * c)) := by
    have hc2 : c ≤ Real.sqrt p := hcbig
    have hpos : 0 < 2 * Real.pi * c := by positivity
    rw [Real.log_div hpR0.ne' hpos.ne', Real.log_mul (by positivity) hc.ne']
    have hlc : Real.log c ≤ Real.log p / 2 := by
      rw [show Real.log p / 2 = Real.log (Real.sqrt p) by
        rw [Real.log_sqrt hpR0.le]]
      exact Real.log_le_log hc hc2
    linarith
  have hD : Real.log p / 4 ≤
      completedShellEnergy tiltedUnitSpline (c / p) - flipCoupling p -
        completedShellEnergy tiltedUnitSpline c := by
    linarith
  have hlaw := margin_mul_le_of_primeFlip_resolutionThreshold_lt contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero paperFT_tiltedUnitSpline_real_ne_zero hp hlt (by linarith)
  -- `κ_p² ≤ 64 log² p/p`
  have hκ2 : flipCoupling p ^ 2 ≤ 64 * Real.log p ^ 2 / p := by
    have hκ0 : 0 ≤ flipCoupling p := by
      unfold flipCoupling
      exact div_nonneg (by positivity) (by linarith)
    calc flipCoupling p ^ 2 ≤ (8 * Real.log p / Real.sqrt p) ^ 2 := pow_le_pow_left₀ hκ0 hκ 2
      _ = 64 * Real.log p ^ 2 / p := by
          rw [div_pow, Real.sq_sqrt hpR0.le]
          ring
  -- the spline floor of the margin
  have hfloor : C₀ / m ^ 7 ≤ completedShellEnergy tiltedUnitSpline c := by
    have h := CriticalArithmeticCorrelationTheory.tiltedUnitSpline_completedConductorEnergy_ge_polynomial_floor
      hm1 one_pos
    have hanti := completedConductorEnergy_anti contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
      integral_tiltedUnitSpline_sq_pos hc hcm one_pos
    simp only [completedConductorEnergy_one] at h hanti
    exact h.trans hanti
  have hE0 : 0 ≤ completedShellEnergy tiltedUnitSpline c := le_trans (by positivity) hfloor
  -- combine: `C₀/m⁷ · log p ≤ 4 E D ≤ 64 log² p/p`
  have h1 : 4 * (C₀ / m ^ 7) * (Real.log p / 4) ≤ 64 * Real.log p ^ 2 / p := by
    calc 4 * (C₀ / m ^ 7) * (Real.log p / 4) ≤
        4 * completedShellEnergy tiltedUnitSpline c *
          (completedShellEnergy tiltedUnitSpline (c / p) - flipCoupling p -
            completedShellEnergy tiltedUnitSpline c) := by
          gcongr
      _ ≤ flipCoupling p ^ 2 := hlaw
      _ ≤ 64 * Real.log p ^ 2 / p := hκ2
  have hm70 : 0 < m ^ 7 := by positivity
  have h1' : C₀ * Real.log p / m ^ 7 ≤ 64 * Real.log p ^ 2 / p := by
    have : 4 * (C₀ / m ^ 7) * (Real.log p / 4) = C₀ * Real.log p / m ^ 7 := by ring
    linarith
  rw [div_le_div_iff₀ hm70 hpR0] at h1'
  have h2 : C₀ * p ≤ 64 * Real.log p * m ^ 7 := by
    have h3 : Real.log p * (C₀ * p) ≤ Real.log p * (64 * Real.log p * m ^ 7) := by nlinarith
    exact le_of_mul_le_mul_left h3 hlogp0
  calc min (C₀ / 64) 1 * p ≤ C₀ / 64 * p := mul_le_mul_of_nonneg_right hκC hpR0.le
    _ ≤ Real.log p * m ^ 7 := by linarith

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
