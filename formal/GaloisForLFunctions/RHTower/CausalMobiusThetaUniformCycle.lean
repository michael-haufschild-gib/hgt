import GaloisForLFunctions.RHTower.CausalMobiusThetaPrimorialInnovation

/-!
# The uniform-cycle carrier of the causal theta source

On the finite cycle `ℤ/Mℤ`, `M = R_N`, let `V_g` be uniform conditional averaging onto functions of
the residue modulo `g ∣ M`, and `U_l = V_{R_l}`.  For the fractional atoms `f_d(r) = {r/d}`:

* `V_g f_d(r) = [(r mod h) + (d − h)/2]/d` with `h = gcd(g, d)`; in particular **(11)** for `g ∣ d`;
* **(8)** `(U_p − U_{p−1}) f_d = 0` when `p ∤ d`;
* **(12)** `(U_p − U_{p−1}) f_{pab}(r) = ψ_p(⌊r/a⌋)/b` for the smooth/rough factorization `d = pab`;
* the extended observer `a_N(r) = [g(r/N) − g((r+1)/N)]/√N` (`r ≥ 0`) has exact mean zero, and its
  periodization `Q_N(a) = M Σ_{r ≡ a} a_N(r)` gives **(9)** `⟨C_N, q_N⟩_H = ⟨C_N, Q_N⟩_M`;
* **(10)** the prime–cofactor decomposition of `B(N)` with no nonincident prime layers.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## Complete residue systems -/

theorem sum_range_add_mul_mod_eq {n g' : ℕ} (hn : 0 < n) (hcop : Nat.Coprime g' n) (q : ℕ) :
    ∑ j ∈ Finset.range n, (q + g' * j) % n = ∑ i ∈ Finset.range n, i := by
  classical
  have hinj : Set.InjOn (fun j => (q + g' * j) % n) (Finset.range n : Set ℕ) := by
    intro j₁ hj₁ j₂ hj₂ h
    simp only [Finset.coe_range, Set.mem_Iio] at hj₁ hj₂
    have h1 : q + g' * j₁ ≡ q + g' * j₂ [MOD n] := h
    have h2 : g' * j₁ ≡ g' * j₂ [MOD n] := Nat.ModEq.add_left_cancel' q h1
    have h3 : j₁ ≡ j₂ [MOD n] := Nat.ModEq.cancel_left_of_coprime (by
      rw [Nat.gcd_comm]; exact hcop) h2
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hj₁, Nat.mod_eq_of_lt hj₂] at h3
  have himg : (Finset.range n).image (fun j => (q + g' * j) % n) = Finset.range n := by
    refine Finset.eq_of_subset_of_card_le (fun i hi => ?_) ?_
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hi
      exact Finset.mem_range.2 (Nat.mod_lt _ hn)
    · rw [Finset.card_image_of_injOn hinj]
  calc ∑ j ∈ Finset.range n, (q + g' * j) % n =
        ∑ i ∈ (Finset.range n).image (fun j => (q + g' * j) % n), i :=
          (Finset.sum_image (f := fun i => i) hinj).symm
    _ = ∑ i ∈ Finset.range n, i := by rw [himg]

theorem sum_range_add_mul_mod_eq_gcd {c g d : ℕ} (hd : 0 < d) (hg : 0 < g) :
    ∑ j ∈ Finset.range (d / Nat.gcd g d), (c + g * j) % d =
      d / Nat.gcd g d * (c % Nat.gcd g d) + Nat.gcd g d * ∑ i ∈ Finset.range (d / Nat.gcd g d), i := by
  set h := Nat.gcd g d with hh
  have hh0 : 0 < h := Nat.gcd_pos_of_pos_left _ hg
  set n := d / h with hn
  have hdn : d = h * n := (Nat.mul_div_cancel' (Nat.gcd_dvd_right g d)).symm
  have hgn : g = h * (g / h) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left g d)).symm
  have hn0 : 0 < n := Nat.div_pos (Nat.le_of_dvd hd (Nat.gcd_dvd_right g d)) hh0
  have hcop : Nat.Coprime (g / h) n := Nat.coprime_div_gcd_div_gcd hh0
  have hterm : ∀ j, (c + g * j) % d = c % h + h * ((c / h + g / h * j) % n) := by
    intro j
    have hx : c + g * j = c % h + h * (c / h + g / h * j) := by
      conv_lhs => rw [← Nat.mod_add_div c h, hgn]
      ring
    rw [hx, hdn, Nat.mod_mul, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Nat.mod_lt _ hh0),
      Nat.add_mul_div_left _ _ hh0, Nat.div_eq_of_lt (Nat.mod_lt _ hh0), zero_add]
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, smul_eq_mul, ← Finset.mul_sum, sum_range_add_mul_mod_eq hn0 hcop]

/-! ## Uniform averaging on the cycle -/

/-- The fractional atom `f_d(r) = {r/d}`. -/
def fracAtom (d r : ℕ) : ℝ := ((r % d : ℕ) : ℝ) / d

/-- Uniform conditional average modulo `g` over one period `M`. -/
def cycleAverage (M g : ℕ) (f : ℕ → ℝ) (r : ℕ) : ℝ :=
  (g : ℝ) / M * ∑ t ∈ Finset.range (M / g), f (r % g + g * t)

theorem sum_range_mul_period_eq {F : ℕ → ℝ} {n : ℕ} (hF : ∀ t, F (t + n) = F t) (s : ℕ) :
    ∑ t ∈ Finset.range (n * s), F t = s * ∑ j ∈ Finset.range n, F j := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    have hper : ∀ m j, F (n * m + j) = F j := by
      intro m
      induction m with
      | zero => simp
      | succ m ihm => intro j; rw [show n * (m + 1) + j = (n * m + j) + n by ring, hF, ihm]
    rw [Finset.sum_congr rfl fun j _ => hper s j]
    push_cast; ring

/-- **The cyclic average of a fractional atom**: `V_g f_d(r) = [(r mod h) + (d − h)/2]/d`,
`h = gcd(g, d)`, whenever `g, d ∣ M`. -/
theorem cycleAverage_fracAtom {M g d : ℕ} (hM0 : 0 < M) (hg : g ∣ M) (hd : d ∣ M) (hg0 : 0 < g)
    (hd0 : 0 < d) (r : ℕ) :
    cycleAverage M g (fracAtom d) r =
      (((r % Nat.gcd g d : ℕ) : ℝ) + ((d : ℝ) - Nat.gcd g d) / 2) / d := by
  set h := Nat.gcd g d with hh
  have hh0 : 0 < h := Nat.gcd_pos_of_pos_left _ hg0
  set n := d / h with hn
  have hdn : d = h * n := (Nat.mul_div_cancel' (Nat.gcd_dvd_right g d)).symm
  have hn0 : 0 < n := Nat.div_pos (Nat.le_of_dvd hd0 (Nat.gcd_dvd_right g d)) hh0
  -- `g n = lcm(g, d)` divides `M`
  have hgn : g * n ∣ M := by
    have : g * n = Nat.lcm g d := by
      rw [Nat.lcm, hn, Nat.mul_div_assoc _ (Nat.gcd_dvd_right g d)]
    rw [this]; exact Nat.lcm_dvd hg hd
  obtain ⟨s, hs⟩ := hgn
  have hMg : M / g = n * s := by
    rw [hs, mul_assoc, Nat.mul_div_cancel_left _ hg0]
  set c := r % g
  have hper : ∀ t, fracAtom d (c + g * (t + n)) = fracAtom d (c + g * t) := by
    intro t
    unfold fracAtom
    congr 2
    have : c + g * (t + n) = (c + g * t) + (g / h) * d := by
      rw [hdn, mul_add, ← mul_assoc, Nat.div_mul_cancel (Nat.gcd_dvd_left g d)]; ring
    rw [this, Nat.add_mul_mod_self_right]
  rw [cycleAverage, hMg, sum_range_mul_period_eq (F := fun t => fracAtom d (c + g * t)) hper s]
  have hsum := sum_range_add_mul_mod_eq_gcd (c := c) hd0 hg0
  rw [← hh, ← hn] at hsum
  have hgauss := Finset.sum_range_id_mul_two n
  have hc : c % h = r % h := Nat.mod_mod_of_dvd r (Nat.gcd_dvd_left g d)
  simp only [fracAtom]
  rw [← Finset.sum_div, show (∑ x ∈ Finset.range n, (((c + g * x) % d : ℕ) : ℝ)) =
    (((∑ x ∈ Finset.range n, (c + g * x) % d) : ℕ) : ℝ) by push_cast; rfl, hsum, ← hc]
  have hs0 : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · rw [h0, mul_zero] at hs; omega
    · exact h0
  have hMR : (M : ℝ) = g * n * s := by rw [hs]; push_cast; ring
  have hdR : (d : ℝ) = h * n := by rw [hdn]; push_cast; ring
  have hSR : ∑ i ∈ Finset.range n, (i : ℝ) = n * ((n : ℝ) - 1) / 2 := by
    have h1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn0]; simp
    have h2 : (((∑ i ∈ Finset.range n, i) * 2 : ℕ) : ℝ) = ((n * (n - 1) : ℕ) : ℝ) := by
      rw [hgauss]
    push_cast at h2
    rw [h1] at h2
    linarith
  push_cast
  rw [hSR, hMR, hdR]
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs0
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh0
  field_simp

/-- **(11)** For `g ∣ d ∣ M`: `V_g f_d(r) = [(r mod g) + (d − g)/2]/d`. -/
theorem cycleAverage_fracAtom_of_dvd {M g d : ℕ} (hM0 : 0 < M) (hgd : g ∣ d) (hd : d ∣ M) (hg0 : 0 < g)
    (hd0 : 0 < d) (r : ℕ) :
    cycleAverage M g (fracAtom d) r = (((r % g : ℕ) : ℝ) + ((d : ℝ) - g) / 2) / d := by
  rw [cycleAverage_fracAtom hM0 (hgd.trans hd) hd hg0 hd0, Nat.gcd_eq_left hgd]

open DeletionResidueMartingale in
theorem prime_le_of_dvd_primorial {q n : ℕ} (hq : q.Prime) (h : q ∣ primorial n) : q ≤ n := by
  unfold primorial at h
  obtain ⟨p, hp, hqp⟩ := (Prime.dvd_finsetProd_iff hq.prime _).1 h
  have hpp := (Finset.mem_filter.1 hp).2
  have := (Nat.prime_dvd_prime_iff_eq hq hpp).1 hqp
  have := Finset.mem_range.1 (Finset.mem_filter.1 hp).1
  omega

theorem coprime_primorial_of_primeFactors_gt {n b : ℕ} (hb0 : 0 < b) (hb : ∀ q ∈ b.primeFactors, n < q) :
    Nat.Coprime (primorial n) b := by
  refine Nat.coprime_of_dvd fun k hk h1 h2 => ?_
  have h3 := prime_le_of_dvd_primorial hk h1
  have := hb k (Nat.mem_primeFactors.2 ⟨hk, h2, hb0.ne'⟩)
  omega

/-- `R_p = p R_{p−1}` for a prime `p`. -/
theorem primorial_prime_eq {p : ℕ} (hp : p.Prime) : primorial p = p * primorial (p - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  rw [DeletionResidueMartingale.primorial_succ_eq, if_pos hp, Nat.add_sub_cancel]

theorem not_dvd_primorial_pred {p : ℕ} (hp : p.Prime) : ¬ p ∣ primorial (p - 1) := fun h => by
  have := prime_le_of_dvd_primorial hp h
  have := hp.two_le
  omega

/-- The smooth part: `gcd(R_{p−1}, p a b) = a`. -/
theorem gcd_primorial_pred_smooth_rough {p a b : ℕ} (hp : p.Prime) (ha : a ∣ primorial (p - 1))
    (hb0 : 0 < b) (hb : ∀ q ∈ b.primeFactors, p < q) : Nat.gcd (primorial (p - 1)) (p * a * b) = a := by
  apply Nat.dvd_antisymm
  · have hcop : Nat.Coprime (Nat.gcd (primorial (p - 1)) (p * a * b)) (p * b) := by
      refine Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) ?_
      refine Nat.Coprime.mul_right ?_ (coprime_primorial_of_primeFactors_gt hb0 fun q hq => by have := hb q hq; omega)
      exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_primorial_pred hp)))
    have : Nat.gcd (primorial (p - 1)) (p * a * b) ∣ a * (p * b) := by
      rw [show a * (p * b) = p * a * b by ring]; exact Nat.gcd_dvd_right _ _
    exact hcop.dvd_of_dvd_mul_right this
  · exact Nat.dvd_gcd ha (Dvd.intro (p * b) (by ring))

/-- The smooth part with the new prime: `gcd(R_p, p a b) = p a`. -/
theorem gcd_primorial_smooth_rough {p a b : ℕ} (hp : p.Prime) (ha : a ∣ primorial (p - 1))
    (hb0 : 0 < b) (hb : ∀ q ∈ b.primeFactors, p < q) : Nat.gcd (primorial p) (p * a * b) = p * a := by
  rw [primorial_prime_eq hp]
  apply Nat.dvd_antisymm
  · have hcop : Nat.Coprime (Nat.gcd (p * primorial (p - 1)) (p * a * b)) b :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) (by
        rw [← primorial_prime_eq hp]; exact coprime_primorial_of_primeFactors_gt hb0 hb)
    exact hcop.dvd_of_dvd_mul_right (Nat.gcd_dvd_right _ _)
  · exact Nat.dvd_gcd (Nat.mul_dvd_mul_left p ha) ⟨b, rfl⟩

/-- The layer `(U_p − U_{p−1}) f` on the cycle. -/
def cycleLayer (M p : ℕ) (f : ℕ → ℝ) (r : ℕ) : ℝ :=
  cycleAverage M (primorial p) f r - cycleAverage M (primorial (p - 1)) f r

/-- The centered sawtooth `ψ_p(j) = [(j mod p) − (p−1)/2]/p`. -/
def centeredSawtooth (p j : ℕ) : ℝ := (((j % p : ℕ) : ℝ) - ((p : ℝ) - 1) / 2) / p

/-- **(8)** `(U_p − U_{p−1}) f_d = 0` when `p ∤ d`. -/
theorem cycleLayer_fracAtom_eq_zero {M p d : ℕ} (hM0 : 0 < M) (hp : p.Prime) (hpM : primorial p ∣ M)
    (hd : d ∣ M) (hd0 : 0 < d) (hpd : ¬ p ∣ d) (r : ℕ) : cycleLayer M p (fracAtom d) r = 0 := by
  have hpM' : primorial (p - 1) ∣ M := (DeletionResidueMartingale.primorial_dvd_primorial (by omega)).trans hpM
  rw [cycleLayer, cycleAverage_fracAtom hM0 hpM hd (primorial_pos _) hd0,
    cycleAverage_fracAtom hM0 hpM' hd (primorial_pos _) hd0, primorial_prime_eq hp,
    Nat.Coprime.gcd_mul_left_cancel _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd), sub_self]

/-- **(12)** `(U_p − U_{p−1}) f_{pab}(r) = ψ_p(⌊r/a⌋)/b` for `a ∣ R_{p−1}` and `b` with all prime
factors larger than `p`. -/
theorem cycleLayer_fracAtom_smooth_rough {M p a b : ℕ} (hM0 : 0 < M) (hp : p.Prime) (hpM : primorial p ∣ M)
    (ha : a ∣ primorial (p - 1)) (hb : ∀ q ∈ b.primeFactors, p < q) (hb0 : 0 < b)
    (hd : p * a * b ∣ M) (r : ℕ) :
    cycleLayer M p (fracAtom (p * a * b)) r = centeredSawtooth p (r / a) / b := by
  have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha (primorial_pos _)
  have hd0 : 0 < p * a * b := by have := hp.pos; positivity
  have hpM' : primorial (p - 1) ∣ M := (DeletionResidueMartingale.primorial_dvd_primorial (by omega)).trans hpM
  rw [cycleLayer, cycleAverage_fracAtom hM0 hpM hd (primorial_pos _) hd0,
    cycleAverage_fracAtom hM0 hpM' hd (primorial_pos _) hd0, gcd_primorial_smooth_rough hp ha hb0 hb,
    gcd_primorial_pred_smooth_rough hp ha hb0 hb, centeredSawtooth]
  have hmod : r % (p * a) = r % a + a * (r / a % p) := by rw [mul_comm p a, Nat.mod_mul]
  rw [hmod]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have haR : (0 : ℝ) < a := by exact_mod_cast ha0
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb0
  push_cast
  field_simp
  ring

/-! ## The periodized observer -/

/-- The extended observer `a_N(r) = [g(r/N) − g((r+1)/N)]/√N`, `r ≥ 0`. -/
def thetaIncrement (N r : ℕ) : ℝ :=
  (thetaCuspSeed (r / N) - thetaCuspSeed (((r : ℝ) + 1) / N)) / Real.sqrt N

theorem thetaIncrement_succ (N j : ℕ) :
    thetaIncrement N (j + 1) = thetaCellWavelet N (j + 1) * DeletionResidueMartingale.cellWeight j := by
  rw [thetaCellWavelet_mul_cellWeight, thetaIncrement]

theorem thetaIncrement_zero (N : ℕ) : thetaIncrement N 0 = -(thetaCuspSeed (1 / N) / Real.sqrt N) := by
  simp [thetaIncrement, thetaCuspSeed_zero, neg_div]

theorem summable_abs_thetaIncrement {N : ℕ} (hN : 1 ≤ N) : Summable fun r => |thetaIncrement N r| := by
  have h1 := summable_abs_thetaCuspSeed_div hN
  have h2 : Summable fun r : ℕ => |thetaCuspSeed (((r : ℝ) + 1) / N)| := by
    have := (summable_nat_add_iff 1).2 h1
    exact this.congr fun r => by push_cast; rfl
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun r => ?_) ((h1.add h2).div_const (Real.sqrt N))
  rw [thetaIncrement, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right (abs_sub _ _) (Real.sqrt_nonneg _)

/-- The extended observer has exact mean zero: `Σ_{r≥0} a_N(r) = 0`. -/
theorem hasSum_thetaIncrement {N : ℕ} (hN : 1 ≤ N) : HasSum (thetaIncrement N) 0 := by
  set u : ℕ → ℝ := fun r => thetaCuspSeed (r / N) / Real.sqrt N
  have hu : Summable u := (summable_thetaCuspSeed_div hN).div_const _
  have h2 : HasSum (fun r => u (r + 1)) (∑' r, u r - u 0) := by
    simpa using (hasSum_nat_add_iff' 1).2 hu.hasSum
  have h := hu.hasSum.sub h2
  have hu0 : u 0 = 0 := by simp [u, thetaCuspSeed_zero]
  rw [sub_sub_cancel, hu0] at h
  refine h.congr_fun fun r => ?_
  simp only [u, thetaIncrement]
  push_cast
  ring

/-- `Q_N(a) = M Σ_{r ≡ a (M)} a_N(r)`. -/
def periodizedObserver (M N a : ℕ) : ℝ := M * ∑' k, thetaIncrement N (a + M * k)

/-- The normalized uniform pairing `⟨u, v⟩_M = M^{−1} Σ_{a<M} u(a) v(a)`. -/
def cyclePairing (M : ℕ) (u v : ℕ → ℝ) : ℝ := (M : ℝ)⁻¹ * ∑ a ∈ Finset.range M, u a * v a

theorem periodic_apply_add_mul {φ : ℕ → ℝ} {M : ℕ} (hφ : ∀ r, φ (r + M) = φ r) (b k : ℕ) :
    φ (b + M * k) = φ b := by
  induction k with
  | zero => simp
  | succ k ih => rw [show b + M * (k + 1) = (b + M * k) + M by ring, hφ, ih]

/-- Periodic observables pair with `a_N` through the periodized observer. -/
theorem tsum_mul_thetaIncrement_eq_cyclePairing {M N : ℕ} (hM : 0 < M) (hN : 1 ≤ N) {φ : ℕ → ℝ}
    (hφ : ∀ r, φ (r + M) = φ r) {C : ℝ} (hb : ∀ r, |φ r| ≤ C) :
    ∑' r, φ r * thetaIncrement N r = cyclePairing M φ (periodizedObserver M N) := by
  have hs : Summable fun r => φ r * thetaIncrement N r :=
    Summable.of_norm_bounded ((summable_abs_thetaIncrement hN).mul_left C) fun r => by
      rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul_of_nonneg_right (hb r) (abs_nonneg _)
  rw [DeletionResidueMartingale.tsum_eq_sum_range_tsum_progression hs hM, cyclePairing, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp_rw [periodic_apply_add_mul hφ b]
  rw [tsum_mul_left, periodizedObserver]
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp

theorem cyclePairing_const_periodizedObserver {M N : ℕ} (hM : 0 < M) (hN : 1 ≤ N) (c : ℝ) :
    cyclePairing M (fun _ => c) (periodizedObserver M N) = 0 := by
  rw [← tsum_mul_thetaIncrement_eq_cyclePairing hM hN (φ := fun _ => c) (fun _ => rfl) (C := |c|)
    (fun _ => le_rfl), tsum_mul_left, (hasSum_thetaIncrement hN).tsum_eq, mul_zero]

/-! ## (9) The physical pairing is the uniform pairing -/

theorem moebiusCell_eq_sum_fracAtom (N r : ℕ) :
    moebiusCell N r = ∑ i ∈ Finset.range N, ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) *
      fracAtom (i + 1) r := by
  rw [moebiusCell, DeletionCoefficientTransfer.cell]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fracAtom]
  push_cast
  ring

theorem moebius_ne_zero_dvd_primorial {N i : ℕ} (hi : i < N)
    (hμ : ArithmeticFunction.moebius (i + 1) ≠ 0) : i + 1 ∣ primorial N := by
  have hsq := ArithmeticFunction.moebius_ne_zero_iff_squarefree.1 hμ
  refine DeletionResidueMartingale.squarefree_dvd_primorial hsq fun q hq => ?_
  have := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hq)
  omega

theorem moebiusCell_add_primorial (N r : ℕ) : moebiusCell N (r + primorial N) = moebiusCell N r := by
  rw [moebiusCell_eq_sum_fracAtom, moebiusCell_eq_sum_fracAtom]
  refine Finset.sum_congr rfl fun i hi => ?_
  by_cases hμ : ArithmeticFunction.moebius (i + 1) = 0
  · simp [hμ]
  · obtain ⟨k, hk⟩ := moebius_ne_zero_dvd_primorial (Finset.mem_range.1 hi) hμ
    rw [fracAtom, fracAtom, hk, Nat.add_mul_mod_self_left]

/-- **(9)** `B(N) = ⟨C_N, Q_N⟩_M + e_N` on the cycle `M = R_N`. -/
theorem causalMobiusThetaTail_natCast_eq_cyclePairing {N : ℕ} (hN : 1 ≤ N) :
    causalMobiusThetaTail N =
      cyclePairing (primorial N) (moebiusCell N) (periodizedObserver (primorial N) N) +
        thetaCellDefect N := by
  rw [causalMobiusThetaTail_natCast_eq_cell_pairing hN]
  congr 1
  have hb : ∀ r, |moebiusCell N r| ≤ N := fun r => abs_moebiusCell_le N r
  rw [← tsum_mul_thetaIncrement_eq_cyclePairing (primorial_pos N) hN (moebiusCell_add_primorial N) hb]
  have hs : Summable fun r => moebiusCell N r * thetaIncrement N r :=
    Summable.of_norm_bounded ((summable_abs_thetaIncrement hN).mul_left (N : ℝ)) fun r => by
      rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul_of_nonneg_right (hb r) (abs_nonneg _)
  rw [hs.tsum_eq_zero_add, moebiusCell_zero, zero_mul, zero_add]
  refine tsum_congr fun j => ?_
  rw [thetaIncrement_succ]
  ring

/-! ## (10) The prime–cofactor decomposition -/

theorem cycleAverage_sum (M g : ℕ) (s : Finset ℕ) (c : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (r : ℕ) :
    cycleAverage M g (fun x => ∑ i ∈ s, c i * f i x) r = ∑ i ∈ s, c i * cycleAverage M g (f i) r := by
  simp only [cycleAverage, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun t _ => by ring

theorem cycleLayer_sum (M p : ℕ) (s : Finset ℕ) (c : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (r : ℕ) :
    cycleLayer M p (fun x => ∑ i ∈ s, c i * f i x) r = ∑ i ∈ s, c i * cycleLayer M p (f i) r := by
  rw [cycleLayer, cycleAverage_sum, cycleAverage_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [cycleLayer]; ring

theorem cycleAverage_self_of_periodic {M : ℕ} (hM : 0 < M) {f : ℕ → ℝ} (hf : ∀ r, f (r + M) = f r)
    (r : ℕ) : cycleAverage M M f r = f r := by
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [cycleAverage, Nat.div_self hM, Finset.sum_range_one, mul_zero, add_zero, div_self hMR, one_mul]
  conv_rhs => rw [← Nat.mod_add_div r M]
  exact (periodic_apply_add_mul hf _ _).symm

theorem cycleAverage_one (M : ℕ) (f : ℕ → ℝ) (r : ℕ) :
    cycleAverage M 1 f r = (M : ℝ)⁻¹ * ∑ t ∈ Finset.range M, f t := by
  simp [cycleAverage, Nat.mod_one]

theorem cyclePairing_sub_left (M : ℕ) (u v w : ℕ → ℝ) :
    cyclePairing M (fun r => u r - v r) w = cyclePairing M u w - cyclePairing M v w := by
  simp only [cyclePairing, sub_mul, Finset.sum_sub_distrib, mul_sub]

theorem cyclePairing_sum_left (M : ℕ) (s : Finset ℕ) (c : ℕ → ℝ) (u : ℕ → ℕ → ℝ) (w : ℕ → ℝ) :
    cyclePairing M (fun r => ∑ i ∈ s, c i * u i r) w = ∑ i ∈ s, c i * cyclePairing M (u i) w := by
  simp only [cyclePairing, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by ring

theorem cyclePairing_congr_left (M : ℕ) {u v : ℕ → ℝ} (h : ∀ a, u a = v a) (w : ℕ → ℝ) :
    cyclePairing M u w = cyclePairing M v w := by
  simp only [cyclePairing, h]

/-- The uniform projections telescope over primes; the constant layer pairs to zero. -/
theorem cyclePairing_eq_sum_primeLayers {N : ℕ} (hN : 1 ≤ N) {f : ℕ → ℝ}
    (hf : ∀ r, f (r + primorial N) = f r) :
    cyclePairing (primorial N) f (periodizedObserver (primorial N) N) =
      ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        cyclePairing (primorial N) (cycleLayer (primorial N) p f) (periodizedObserver (primorial N) N) := by
  set M := primorial N
  have hM : 0 < M := primorial_pos N
  have htel : ∀ r, f r = cycleAverage M (primorial 0) f r +
      ∑ l ∈ Finset.Ioc 0 N, cycleLayer M l f r := by
    intro r
    have h := sum_Ioc_sub_eq (fun l => cycleAverage M (primorial l) f r) (Nat.zero_le N)
    rw [show (∑ l ∈ Finset.Ioc 0 N, cycleLayer M l f r) =
      ∑ l ∈ Finset.Ioc 0 N, (cycleAverage M (primorial l) f r - cycleAverage M (primorial (l - 1)) f r) from rfl,
      h, cycleAverage_self_of_periodic hM hf]
    ring
  have h0 : primorial 0 = 1 := by decide
  rw [cyclePairing_congr_left M htel]
  have hsplit : cyclePairing M (fun r => cycleAverage M (primorial 0) f r +
      ∑ l ∈ Finset.Ioc 0 N, cycleLayer M l f r) (periodizedObserver M N) =
      cyclePairing M (fun _ => (M : ℝ)⁻¹ * ∑ t ∈ Finset.range M, f t) (periodizedObserver M N) +
        ∑ l ∈ Finset.Ioc 0 N, cyclePairing M (cycleLayer M l f) (periodizedObserver M N) := by
    have := cyclePairing_sum_left M (Finset.Ioc 0 N) (fun _ => 1) (fun l => cycleLayer M l f)
      (periodizedObserver M N)
    simp only [one_mul] at this
    rw [← this, cyclePairing, cyclePairing, cyclePairing, ← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [h0, cycleAverage_one]
    ring
  rw [hsplit, cyclePairing_const_periodizedObserver hM hN, zero_add, Finset.sum_filter]
  rw [show Finset.Ioc 0 N = Finset.Icc 1 N from rfl]
  refine Finset.sum_congr rfl fun l hl => ?_
  split_ifs with hp
  · rfl
  · have hl1 : 1 ≤ l := (Finset.mem_Icc.1 hl).1
    obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    have hR : primorial (m + 1) = primorial m := DeletionResidueMartingale.primorial_succ_of_not_prime hp
    have hz : ∀ r, cycleLayer M (m + 1) f r = 0 := fun r => by
      rw [cycleLayer, hR, Nat.add_sub_cancel, sub_self]
    rw [cyclePairing_congr_left M hz]
    simp [cyclePairing]

theorem moebius_prime_mul_eq_ite {p m : ℕ} (hp : p.Prime) :
    ((ArithmeticFunction.moebius (p * m) : ℤ) : ℝ) =
      if p ∣ m then 0 else -((ArithmeticFunction.moebius m : ℤ) : ℝ) := by
  split_ifs with hpm
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree]
    · simp
    · intro hsq
      have := hsq p (by obtain ⟨k, rfl⟩ := hpm; exact ⟨k, by ring⟩)
      exact hp.one_lt.ne' (Nat.isUnit_iff.1 this)
  · rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm), ArithmeticFunction.moebius_apply_prime hp]
    push_cast; ring

/-- The prime layer of the literal source: only incident atoms survive. -/
theorem cycleLayer_moebiusCell_eq {N p : ℕ} (hp : p.Prime) (hpN : p ≤ N) (r : ℕ) :
    cycleLayer (primorial N) p (moebiusCell N) r =
      -cycleLayer (primorial N) p (fracAtom p) r -
        ∑ m ∈ (Finset.Icc 2 (N / p)).filter (fun m => ¬ p ∣ m),
          ((ArithmeticFunction.moebius m : ℤ) : ℝ) * cycleLayer (primorial N) p (fracAtom (p * m)) r := by
  set M := primorial N
  have hM : 0 < M := primorial_pos N
  have hpM : primorial p ∣ M := DeletionResidueMartingale.primorial_dvd_primorial hpN
  have hC : moebiusCell N = fun x => ∑ i ∈ Finset.range N,
      ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) * fracAtom (i + 1) x :=
    funext fun x => moebiusCell_eq_sum_fracAtom N x
  rw [hC, cycleLayer_sum, DeletionResidueMartingale.sum_range_succ_eq_sum_Icc_one N
    (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ) * cycleLayer M p (fracAtom d) r)]
  have hfilter : ∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * cycleLayer M p (fracAtom d) r =
      ∑ d ∈ (Finset.Icc 1 N).filter (p ∣ ·), ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        cycleLayer M p (fracAtom d) r := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d hd => ?_
    split_ifs with hpd
    · rfl
    · by_cases hμ : ArithmeticFunction.moebius d = 0
      · simp [hμ]
      · have hd1 := Finset.mem_Icc.1 hd
        have hdM : d ∣ M := by
          have := moebius_ne_zero_dvd_primorial (N := N) (i := d - 1) (by omega)
            (by rwa [Nat.sub_add_cancel hd1.1])
          rwa [Nat.sub_add_cancel hd1.1] at this
        rw [cycleLayer_fracAtom_eq_zero hM hp hpM hdM (by omega) hpd, mul_zero]
  rw [hfilter, sum_Icc_filter_dvd_eq _ hp.pos]
  have hNp : 1 ≤ N / p := (Nat.le_div_iff_mul_le hp.pos).2 (by simpa using hpN)
  rw [← Finset.sum_erase_add _ _ (Finset.mem_Icc.2 ⟨le_rfl, hNp⟩)]
  have herase : (Finset.Icc 1 (N / p)).erase 1 = Finset.Icc 2 (N / p) := by
    ext m; simp only [Finset.mem_erase, Finset.mem_Icc]; omega
  rw [herase, mul_one, ArithmeticFunction.moebius_apply_prime hp, Finset.sum_filter]
  have hsum : ∑ m ∈ Finset.Icc 2 (N / p), ((ArithmeticFunction.moebius (p * m) : ℤ) : ℝ) *
      cycleLayer M p (fracAtom (p * m)) r =
      -∑ m ∈ Finset.Icc 2 (N / p), (if ¬ p ∣ m then ((ArithmeticFunction.moebius m : ℤ) : ℝ) *
        cycleLayer M p (fracAtom (p * m)) r else 0) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [moebius_prime_mul_eq_ite hp]
    split_ifs <;> simp_all
  rw [hsum]
  push_cast
  ring

/-- **(10)** The prime–cofactor decomposition: no nonincident prime layer enters,
`B(N) = −Σ_p ⟨(U_p − U_{p−1})f_p, Q_N⟩_M − Σ_{p, m ≥ 2, p ∤ m} μ(m) ⟨(U_p − U_{p−1})f_{pm}, Q_N⟩_M + e_N`. -/
theorem causalMobiusThetaTail_natCast_eq_primeCofactor {N : ℕ} (hN : 1 ≤ N) :
    causalMobiusThetaTail N =
      -(∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
          cyclePairing (primorial N) (cycleLayer (primorial N) p (fracAtom p))
            (periodizedObserver (primorial N) N)) -
        (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
          ∑ m ∈ (Finset.Icc 2 (N / p)).filter (fun m => ¬ p ∣ m),
            ((ArithmeticFunction.moebius m : ℤ) : ℝ) * cyclePairing (primorial N)
              (cycleLayer (primorial N) p (fracAtom (p * m))) (periodizedObserver (primorial N) N)) +
        thetaCellDefect N := by
  rw [causalMobiusThetaTail_natCast_eq_cyclePairing hN,
    cyclePairing_eq_sum_primeLayers hN (moebiusCell_add_primorial N)]
  congr 1
  set M := primorial N
  set Q := periodizedObserver M N
  have hp_eq : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      cyclePairing M (cycleLayer M p (moebiusCell N)) Q =
        -cyclePairing M (cycleLayer M p (fracAtom p)) Q -
          ∑ m ∈ (Finset.Icc 2 (N / p)).filter (fun m => ¬ p ∣ m),
            ((ArithmeticFunction.moebius m : ℤ) : ℝ) * cyclePairing M (cycleLayer M p (fracAtom (p * m))) Q := by
    intro p hp
    obtain ⟨hp1, hpp⟩ := Finset.mem_filter.1 hp
    rw [cyclePairing_congr_left M (cycleLayer_moebiusCell_eq hpp (Finset.mem_Icc.1 hp1).2)]
    simp only [cyclePairing, sub_mul, neg_mul, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      Finset.sum_mul, mul_sub, mul_neg, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [Finset.sum_congr rfl hp_eq, Finset.sum_sub_distrib, Finset.sum_neg_distrib]

/-- `U_N C_N = C_N`: the literal source is fixed by the top uniform average. -/
theorem cycleAverage_primorial_moebiusCell (N r : ℕ) :
    cycleAverage (primorial N) (primorial N) (moebiusCell N) r = moebiusCell N r :=
  cycleAverage_self_of_periodic (primorial_pos N) (moebiusCell_add_primorial N) r

/-! ## (13) The smooth/rough form of a prime layer -/

/-- `H_p(X) = Σ_{b ≤ X, every prime factor of b exceeds p} μ(b)/b`, including `b = 1`. -/
def roughMoebiusSum (p X : ℕ) : ℝ :=
  ∑ b ∈ (Finset.Icc 1 X).filter (fun b => ∀ q ∈ b.primeFactors, p < q),
    ((ArithmeticFunction.moebius b : ℤ) : ℝ) / b

/-- `|H_p(X)| ≤ Σ_{b ≤ X} 1/b ≤ 1 + log X`. -/
theorem abs_roughMoebiusSum_le (p X : ℕ) : |roughMoebiusSum p X| ≤ 1 + Real.log X := by
  have h1 : |roughMoebiusSum p X| ≤ ∑ b ∈ Finset.Icc 1 X, (1 : ℝ) / b := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun b _ _ => abs_nonneg _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [abs_div, Nat.abs_cast]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    have := ArithmeticFunction.abs_moebius_le_one (n := b)
    exact_mod_cast this
  have h2 : ∑ b ∈ Finset.Icc 1 X, (1 : ℝ) / b = harmonic X := by
    rw [DeletionResidueMartingale.natCast_harmonic_eq_sum_range,
      ← DeletionResidueMartingale.sum_range_succ_eq_sum_Icc_one X (fun b => (1 : ℝ) / b)]
    push_cast; rfl
  exact h1.trans (h2 ▸ harmonic_le_one_add_log X)

theorem moebius_smooth_rough {p a b : ℕ} (hp : p.Prime) (ha : a ∣ primorial (p - 1)) (hb0 : 0 < b)
    (hb : ∀ q ∈ b.primeFactors, p < q) :
    ((ArithmeticFunction.moebius (p * a * b) : ℤ) : ℝ) =
      -(((ArithmeticFunction.moebius a : ℤ) : ℝ) * ((ArithmeticFunction.moebius b : ℤ) : ℝ)) := by
  have hpa : Nat.Coprime p a :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => not_dvd_primorial_pred hp (h.trans ha)
  have hpab : Nat.Coprime (p * a) b := by
    refine Nat.Coprime.coprime_dvd_left ?_ (coprime_primorial_of_primeFactors_gt hb0 hb)
    rw [primorial_prime_eq hp]; exact Nat.mul_dvd_mul_left p ha
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hpab,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hpa,
    ArithmeticFunction.moebius_apply_prime hp]
  push_cast; ring

theorem not_squarefree_of_mul_self_dvd {q d : ℕ} (hq : q.Prime) (h : q * q ∣ d) : ¬ Squarefree d :=
  fun hsq => hq.one_lt.ne' (Nat.isUnit_iff.1 (hsq q h))

/-- **(13)** `(U_p − U_{p−1})C_N(r) = −Σ_{a ∣ R_{p−1}, pa ≤ N} μ(a) H_p(N/(pa)) ψ_p(⌊r/a⌋)`. -/
theorem cycleLayer_moebiusCell_eq_smooth_rough {N p : ℕ} (hp : p.Prime) (hpN : p ≤ N) (r : ℕ) :
    cycleLayer (primorial N) p (moebiusCell N) r =
      -∑ a ∈ (primorial (p - 1)).divisors.filter (fun a => p * a ≤ N),
        ((ArithmeticFunction.moebius a : ℤ) : ℝ) * roughMoebiusSum p (N / (p * a)) *
          centeredSawtooth p (r / a) := by
  set M := primorial N
  have hM : 0 < M := primorial_pos N
  have hpM : primorial p ∣ M := DeletionResidueMartingale.primorial_dvd_primorial hpN
  set S := (primorial (p - 1)).divisors.filter (fun a => p * a ≤ N)
  set T : ℕ → Finset ℕ := fun a =>
    (Finset.Icc 1 (N / (p * a))).filter (fun b => ∀ q ∈ b.primeFactors, p < q)
  set μR : ℕ → ℝ := fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)
  have hC : moebiusCell N = fun x => ∑ i ∈ Finset.range N, μR (i + 1) * fracAtom (i + 1) x :=
    funext fun x => moebiusCell_eq_sum_fracAtom N x
  rw [hC, cycleLayer_sum,
    DeletionResidueMartingale.sum_range_succ_eq_sum_Icc_one N (fun d => μR d * cycleLayer M p (fracAtom d) r)]
  have hRHS : -∑ a ∈ S, μR a * roughMoebiusSum p (N / (p * a)) * centeredSawtooth p (r / a) =
      ∑ x ∈ S.sigma T, -(μR x.1 * (μR x.2 / x.2) * centeredSawtooth p (r / x.1)) := by
    rw [Finset.sum_sigma, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [roughMoebiusSum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  rw [hRHS]
  have hmemS : ∀ a, a ∈ S ↔ a ∣ primorial (p - 1) ∧ p * a ≤ N := fun a => by
    simp [S, Nat.mem_divisors, (primorial_pos (p - 1)).ne']
  have hmemT : ∀ a b, b ∈ T a ↔ (1 ≤ b ∧ b ≤ N / (p * a)) ∧ ∀ q ∈ b.primeFactors, p < q := fun a b => by
    simp [T]
  -- the values agree on the sigma set
  have hval : ∀ a b, a ∣ primorial (p - 1) → 1 ≤ b → p * a * b ≤ N → (∀ q ∈ b.primeFactors, p < q) →
      -(μR a * (μR b / b) * centeredSawtooth p (r / a)) =
        μR (p * a * b) * cycleLayer M p (fracAtom (p * a * b)) r := by
    intro a b ha hb1 hN' hb
    have hμ : μR (p * a * b) = -(μR a * μR b) := moebius_smooth_rough hp ha hb1 hb
    by_cases hμb : ArithmeticFunction.moebius b = 0
    · have : μR b = 0 := by simp [μR, hμb]
      rw [hμ, this]; simp
    · have hsq : Squarefree (p * a * b) := by
        rw [← ArithmeticFunction.moebius_ne_zero_iff_squarefree]
        intro h0
        have : μR (p * a * b) = 0 := by simp [μR, h0]
        rw [hμ] at this
        have hμa : μR a ≠ 0 := by
          have hsqa : Squarefree a := (squarefree_primorial (p - 1)).squarefree_of_dvd ha
          simpa [μR] using ArithmeticFunction.moebius_ne_zero_iff_squarefree.2 hsqa
        have hμb' : μR b ≠ 0 := by simpa [μR] using hμb
        exact (neg_ne_zero.2 (mul_ne_zero hμa hμb')) this
      have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha (primorial_pos _)
      have hd0 : 0 < p * a * b := by have := hp.pos; positivity
      have hdM : p * a * b ∣ M := by
        refine DeletionResidueMartingale.squarefree_dvd_primorial hsq fun q hq => ?_
        exact (Nat.le_of_dvd hd0 (Nat.dvd_of_mem_primeFactors hq)).trans hN'
      rw [cycleLayer_fracAtom_smooth_rough hM hp hpM ha hb hb1 hdM, hμ]
      ring
  symm
  refine Finset.sum_bij_ne_zero (fun x _ _ => p * x.1 * x.2) ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hx _
    obtain ⟨ha, hb⟩ := Finset.mem_sigma.1 hx
    obtain ⟨ha1, -⟩ := (hmemS a).1 ha
    obtain ⟨⟨hb1, hb2⟩, -⟩ := (hmemT a b).1 hb
    have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha1 (primorial_pos _)
    have hpa : 0 < p * a := Nat.mul_pos hp.pos ha0
    refine Finset.mem_Icc.2 ⟨Nat.mul_pos hpa hb1, ?_⟩
    have := (Nat.le_div_iff_mul_le hpa).1 hb2
    simpa [mul_comm] using this
  · rintro ⟨a, b⟩ hx _ ⟨a', b'⟩ hx' _ heq
    obtain ⟨ha, hb⟩ := Finset.mem_sigma.1 hx
    obtain ⟨ha', hb'⟩ := Finset.mem_sigma.1 hx'
    obtain ⟨ha1, -⟩ := (hmemS a).1 ha
    obtain ⟨ha1', -⟩ := (hmemS a').1 ha'
    obtain ⟨⟨hb1, -⟩, hbr⟩ := (hmemT a b).1 hb
    obtain ⟨⟨hb1', -⟩, hbr'⟩ := (hmemT a' b').1 hb'
    simp only at heq
    have haa : a = a' := by
      rw [← gcd_primorial_pred_smooth_rough hp ha1 hb1 hbr, heq,
        gcd_primorial_pred_smooth_rough hp ha1' hb1' hbr']
    subst haa
    have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha1 (primorial_pos _)
    have hbb : b = b' := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hp.pos ha0) heq
    subst hbb
    rfl
  · intro d hd hne
    obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.1 hd
    have hμd : ArithmeticFunction.moebius d ≠ 0 := fun h => hne (by simp [μR, h])
    have hsq : Squarefree d := ArithmeticFunction.moebius_ne_zero_iff_squarefree.1 hμd
    have hdM : d ∣ M := by
      have := moebius_ne_zero_dvd_primorial (N := N) (i := d - 1) (by omega)
        (by rwa [Nat.sub_add_cancel hd1])
      rwa [Nat.sub_add_cancel hd1] at this
    have hpd : p ∣ d := by
      by_contra hpd
      exact hne (by rw [cycleLayer_fracAtom_eq_zero hM hp hpM hdM (by omega) hpd, mul_zero])
    set a := Nat.gcd (primorial (p - 1)) d
    have ha1 : a ∣ primorial (p - 1) := Nat.gcd_dvd_left _ _
    have had : a ∣ d := Nat.gcd_dvd_right _ _
    have hpa : Nat.Coprime p a :=
      (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => not_dvd_primorial_pred hp (h.trans ha1)
    have hpad : p * a ∣ d := hpa.mul_dvd_of_dvd_of_dvd hpd had
    obtain ⟨b, hb⟩ := hpad
    have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha1 (primorial_pos _)
    have hb0 : 0 < b := by
      rcases Nat.eq_zero_or_pos b with h0 | h0
      · rw [h0, mul_zero] at hb; omega
      · exact h0
    have hbr : ∀ q ∈ b.primeFactors, p < q := by
      intro q hq
      have hqp := Nat.prime_of_mem_primeFactors hq
      have hqb := Nat.dvd_of_mem_primeFactors hq
      by_contra hle
      rcases (not_lt.1 hle).lt_or_eq with hlt | heq
      · have hqa : q ∣ a := Nat.dvd_gcd
          (DeletionResidueMartingale.prime_dvd_primorial hqp (by omega))
          (hqb.trans ⟨p * a, by rw [hb]; ring⟩)
        have hqq : q * q ∣ d := (Nat.mul_dvd_mul hqa hqb).trans ⟨p, by rw [hb]; ring⟩
        exact not_squarefree_of_mul_self_dvd hqp hqq hsq
      · have hpb : p ∣ b := heq ▸ hqb
        have hqq : p * p ∣ d := (Nat.mul_dvd_mul_left p hpb).trans ⟨a, by rw [hb]; ring⟩
        exact not_squarefree_of_mul_self_dvd hp hqq hsq
    have hpaN : p * a * b ≤ N := hb ▸ hdN
    have hmem : (⟨a, b⟩ : Σ _ : ℕ, ℕ) ∈ S.sigma T := by
      refine Finset.mem_sigma.2 ⟨(hmemS a).2 ⟨ha1, ?_⟩, (hmemT a b).2 ⟨⟨hb0, ?_⟩, hbr⟩⟩
      · exact (Nat.le_mul_of_pos_right _ hb0).trans hpaN
      · exact (Nat.le_div_iff_mul_le (Nat.mul_pos hp.pos ha0)).2 (by rw [mul_comm]; exact hpaN)
    refine ⟨⟨a, b⟩, hmem, ?_, hb.symm⟩
    rw [hval a b ha1 hb0 hpaN hbr, ← hb]
    exact hne
  · rintro ⟨a, b⟩ hx _
    obtain ⟨ha, hb⟩ := Finset.mem_sigma.1 hx
    obtain ⟨ha1, -⟩ := (hmemS a).1 ha
    obtain ⟨⟨hb1, hb2⟩, hbr⟩ := (hmemT a b).1 hb
    have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha1 (primorial_pos _)
    have hpaN : p * a * b ≤ N := by
      have := (Nat.le_div_iff_mul_le (Nat.mul_pos hp.pos ha0)).1 hb2
      simpa [mul_comm] using this
    exact hval a b ha1 hb1 hpaN hbr

/-! ## The smooth/rough prime current -/

theorem abs_centeredSawtooth_le {p : ℕ} (hp : 0 < p) (j : ℕ) : |centeredSawtooth p j| ≤ 1 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hlt : ((j % p : ℕ) : ℝ) ≤ (p : ℝ) - 1 := by
    have := Nat.mod_lt j hp
    have : ((j % p : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast this
    linarith
  have h0 : (0 : ℝ) ≤ ((j % p : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [centeredSawtooth, abs_div, abs_of_pos hpR, div_le_one hpR, abs_le]
  constructor <;> linarith

theorem centeredSawtooth_add_div {p a M : ℕ} (ha : 0 < a) (hpa : p * a ∣ M) (r : ℕ) :
    centeredSawtooth p ((r + M) / a) = centeredSawtooth p (r / a) := by
  obtain ⟨k, rfl⟩ := hpa
  rw [show r + p * a * k = r + a * (p * k) by ring, Nat.add_mul_div_left _ _ ha, centeredSawtooth,
    centeredSawtooth, Nat.add_mul_mod_self_left]

/-- `A_N(a, p) = Σ_{r ≥ 0} a_N(r) ψ_p(⌊r/a⌋)`. -/
def sawtoothObservation (N a p : ℕ) : ℝ := ∑' r, thetaIncrement N r * centeredSawtooth p (r / a)

theorem cyclePairing_centeredSawtooth_eq {M N a p : ℕ} (hM : 0 < M) (hN : 1 ≤ N) (hp : 0 < p)
    (ha : 0 < a) (hpa : p * a ∣ M) :
    cyclePairing M (fun r => centeredSawtooth p (r / a)) (periodizedObserver M N) =
      sawtoothObservation N a p := by
  rw [← tsum_mul_thetaIncrement_eq_cyclePairing hM hN (φ := fun r => centeredSawtooth p (r / a))
    (fun r => centeredSawtooth_add_div ha hpa r) (C := 1) (fun r => abs_centeredSawtooth_le hp _),
    sawtoothObservation]
  exact tsum_congr fun r => mul_comm _ _

/-- The prime layer of `C_N` observed against `Q_N`. -/
theorem cyclePairing_cycleLayer_moebiusCell_eq {N p : ℕ} (hN : 1 ≤ N) (hp : p.Prime) (hpN : p ≤ N) :
    cyclePairing (primorial N) (cycleLayer (primorial N) p (moebiusCell N))
        (periodizedObserver (primorial N) N) =
      -∑ a ∈ (primorial (p - 1)).divisors.filter (fun a => p * a ≤ N),
        ((ArithmeticFunction.moebius a : ℤ) : ℝ) * roughMoebiusSum p (N / (p * a)) *
          sawtoothObservation N a p := by
  set M := primorial N
  have hM : 0 < M := primorial_pos N
  have hA : ∀ a ∈ (primorial (p - 1)).divisors.filter (fun a => p * a ≤ N),
      sawtoothObservation N a p =
        cyclePairing M (fun r => centeredSawtooth p (r / a)) (periodizedObserver M N) := by
    intro a ha
    obtain ⟨ha1, haN⟩ := Finset.mem_filter.1 ha
    have ha0 : 0 < a := Nat.pos_of_mem_divisors ha1
    have hpa : p * a ∣ M := by
      refine DeletionResidueMartingale.squarefree_dvd_primorial ?_ fun q hq => ?_
      · have hsq : Squarefree (primorial p) := squarefree_primorial p
        refine hsq.squarefree_of_dvd ?_
        rw [primorial_prime_eq hp]; exact Nat.mul_dvd_mul_left p (Nat.dvd_of_mem_divisors ha1)
      · exact (Nat.le_of_dvd (Nat.mul_pos hp.pos ha0) (Nat.dvd_of_mem_primeFactors hq)).trans haN
    exact (cyclePairing_centeredSawtooth_eq hM hN hp.pos ha0 hpa).symm
  rw [Finset.sum_congr rfl fun a ha => by rw [hA a ha],
    cyclePairing_congr_left M (cycleLayer_moebiusCell_eq_smooth_rough hp hpN)]
  simp only [cyclePairing, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul, Finset.mul_sum, mul_neg]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **(13) in (9)–(10)**: the exact smooth/rough prime-current form of the theta observation,
`B(N) = −Σ_{p ≤ N} Σ_{a ∣ R_{p−1}, pa ≤ N} μ(a) H_p(N/(pa)) A_N(a, p) + e_N`. -/
theorem causalMobiusThetaTail_natCast_eq_smoothRough {N : ℕ} (hN : 1 ≤ N) :
    causalMobiusThetaTail N =
      -(∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
          ∑ a ∈ (primorial (p - 1)).divisors.filter (fun a => p * a ≤ N),
            ((ArithmeticFunction.moebius a : ℤ) : ℝ) * roughMoebiusSum p (N / (p * a)) *
              sawtoothObservation N a p) +
        thetaCellDefect N := by
  rw [causalMobiusThetaTail_natCast_eq_cyclePairing hN,
    cyclePairing_eq_sum_primeLayers hN (moebiusCell_add_primorial N), ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨hp1, hpp⟩ := Finset.mem_filter.1 hp
  exact cyclePairing_cycleLayer_moebiusCell_eq hN hpp (Finset.mem_Icc.1 hp1).2

end

end RHTower
