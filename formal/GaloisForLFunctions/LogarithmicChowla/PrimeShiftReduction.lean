import GaloisForLFunctions.LogarithmicChowla.ShiftDeviation

/-!
# Prime-shift self-similarity of the Liouville correlations

For `c(d) = L_U(λ(n)λ(n+d))` (`corr`) and every `h`, there are arbitrarily large scales `k` with

`|c(h) − |𝐏_k|⁻¹ Σ_{p∈𝐏_k} c(ph)| ≤ 6ε` (`exists_scale_corr_close`).

* **Identity.** `L(Z(X_k(n), n mod P_k)) = c(h) − avg_{p∈𝐏_k} c(ph)` (`limAvg_devAvg`): the window
  average is removed by shift invariance, and `L(p·1_{p|m} λ(m)λ(m+ph)) = L(λ(pn)λ(pn+ph)) = c(h)`
  by dilation and `λ(p)² = 1` (`limAvg_prime_weight`).
* **Event bound.** Hoeffding makes the event `|Z| ≥ ε` small for the product law of `(X_k, n mod Q_k)`
  and the uniform residue mod `P_k`; the event inequality turns this into
  `μ(A)(2ε²|𝐏_k|/25 − log 2) ≤ I_k + log 2` for the true law (`mass_mul_le`).
* **Good scale.** With weights `w_k = (|𝐏_k| − C)₊/H_k`, `Σ_k w_k = ∞` by the divergence of
  `Σ_p 1/p` (`exists_sum_weights_gt`), so the entropy decrement yields `k ≥ K` with
  `I_k ≤ (ε³/25)|𝐏_k|` and `|𝐏_k| > C = 25 log 2/ε³`; then `μ(A) ≤ 2ε`.
-/

namespace GaloisForLFunctions.LogarithmicChowla

open Finset Filter Real

noncomputable section

variable {U : Ultrafilter ℝ}

/-- The logarithmic correlation `c(d) = L_U(λ(n)λ(n+d))`. -/
def corr (U : Ultrafilter ℝ) (d : ℕ) : ℝ := limAvg U (fun n => lam n * lam (n + d))

theorem bdd_lam_comp (φ : ℕ → ℕ) : Bdd fun n => lam (φ n) := ⟨1, fun _ => abs_lam_le _⟩

theorem bdd_lam_mul_shift (d : ℕ) : Bdd fun n => lam n * lam (n + d) :=
  bdd_lam.mul (bdd_lam.comp_add d)

/-- **Dilation by a prime.** `L(p·1_{p|m} λ(m)λ(m+ph)) = c(h)`. -/
theorem limAvg_prime_weight (hU : (U : Filter ℝ) ≤ atTop) {p : ℕ} (hp : p.Prime) (h : ℕ) :
    limAvg U (fun m => if p ∣ m then (p : ℝ) * (lam m * lam (m + p * h)) else 0) = corr U h := by
  rw [← limAvg_dilate hU (bdd_lam_mul_shift (p * h)) hp.pos]
  unfold corr
  congr 1
  funext n
  rw [show p * n + p * h = p * (n + h) by ring, lam_mul, lam_mul, lam_prime hp]
  ring

/-- **The correlation identity.** `L(Z) = c(h) − avg_{p ∈ 𝐏_k} c(ph)`. -/
theorem limAvg_devAvg (hU : (U : Filter ℝ) ≤ atTop) (h k : ℕ) :
    limAvg U (fun n => devAvg h k (blk (blockLen h k) n) (crtAt k (res (primeProd k) n)))
      = corr U h - (∑ p : primesAt k, corr U ((p : ℕ) * h)) / (primesAt k).card := by
  set N := winLen k with hNdef
  have hc : (0 : ℝ) < (primesAt k).card := by exact_mod_cast card_primesAt_pos k
  have hN : (0 : ℝ) < N := by exact_mod_cast winLen_pos k
  set F : primesAt k → ℕ → ℕ → ℝ := fun p j n =>
    (if (p : ℕ) ∣ n + j then ((p : ℕ) : ℝ) else 0) * (lam (n + j) * lam (n + j + p * h)) with hF
  set G : primesAt k → ℕ → ℕ → ℝ := fun p j n => lam (n + j) * lam (n + j + p * h) with hG
  have hpt : ∀ n, n ≠ 0 →
      devAvg h k (blk (blockLen h k) n) (crtAt k (res (primeProd k) n))
        = (1 / (primesAt k).card) * ∑ p : primesAt k,
            ((1 / N) * ∑ j ∈ range N, (F p j n - G p j n)) := by
    intro n hn
    rw [devAvg, div_eq_inv_mul, one_div]
    congr 1
    refine sum_congr rfl fun p _ => ?_
    rw [res, crtAt_natCast, shiftDev, div_eq_inv_mul, one_div]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    have hjN : j < N := mem_range.mp hj
    have hj1 : j < blockLen h k :=
      lt_of_le_of_lt (Nat.le_add_right j _) (add_mul_lt_blockLen p.2 hjN)
    rw [sv_blk hn hj1, sv_blk hn (add_mul_lt_blockLen p.2 hjN), ← Nat.cast_add]
    simp only [ZMod.natCast_eq_zero_iff, hF, hG, ← add_assoc]
    split_ifs <;> ring
  have hbF : ∀ p j, Bdd (F p j) := fun p j =>
    (bdd_ite (bdd_const _) (bdd_const 0)).mul
      ((bdd_lam_comp fun n => n + j).mul (bdd_lam_comp fun n => n + j + (p : ℕ) * h))
  have hbG : ∀ p j, Bdd (G p j) := fun p j =>
    (bdd_lam_comp fun n => n + j).mul (bdd_lam_comp fun n => n + j + (p : ℕ) * h)
  have hLF : ∀ p j, limAvg U (F p j) = corr U h := by
    intro p j
    have hΦ : Bdd fun m => if (p : ℕ) ∣ m then ((p : ℕ) : ℝ) * (lam m * lam (m + p * h)) else 0 :=
      bdd_ite ((bdd_lam_mul_shift _).const_mul _) (bdd_const 0)
    rw [← limAvg_prime_weight hU (prime_of_mem_primesAt p.2) h,
      ← limAvg_shift_add hU hΦ j]
    congr 1
    funext n
    simp only [hF]
    split_ifs <;> ring_nf
  have hLG : ∀ p : primesAt k, ∀ j, limAvg U (G p j) = corr U ((p : ℕ) * h) := by
    intro p j
    rw [corr, ← limAvg_shift_add hU (bdd_lam_mul_shift ((p : ℕ) * h)) j]
  have hinner : ∀ p : primesAt k, Bdd fun n => (1 / N) * ∑ j ∈ range N, (F p j n - G p j n) :=
    fun p => (bdd_sum _ fun j _ => (hbF p j).sub (hbG p j)).const_mul _
  rw [limAvg_congr_pos hpt, limAvg_const_mul hU (bdd_sum _ fun p _ => hinner p),
    limAvg_sum hU _ fun p _ => hinner p]
  have hstep : ∀ p : primesAt k,
      limAvg U (fun n => (1 / N) * ∑ j ∈ range N, (F p j n - G p j n))
        = corr U h - corr U ((p : ℕ) * h) := by
    intro p
    rw [limAvg_const_mul hU (bdd_sum _ fun j _ => (hbF p j).sub (hbG p j)),
      limAvg_sum hU _ fun j _ => (hbF p j).sub (hbG p j)]
    simp only [fun j => limAvg_sub hU (hbF p j) (hbG p j), hLF, hLG, sum_const, card_range,
      nsmul_eq_mul]
    field_simp
  simp only [hstep]
  simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
  field_simp

/-! ## The event bound -/

/-- The joint observation `((X_k(n), n mod Q_k), n mod P_k)`. -/
def obs (h k n : ℕ) : ((Fin (blockLen h k) → Bool) × ZMod (earlierProd k)) × ZMod (primeProd k) :=
  ((blk (blockLen h k) n, res (earlierProd k) n), res (primeProd k) n)

/-- The deviation of an observation. -/
def obsDev (h k : ℕ)
    (t : ((Fin (blockLen h k) → Bool) × ZMod (earlierProd k)) × ZMod (primeProd k)) : ℝ :=
  devAvg h k t.1.1 (crtAt k t.2)

/-- `|c(h) − avg c(ph)| ≤ ε + (5/2) μ(|Z| ≥ ε)`. -/
theorem abs_corr_sub_le (hU : (U : Filter ℝ) ≤ atTop) (h k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    |corr U h - (∑ p : primesAt k, corr U ((p : ℕ) * h)) / (primesAt k).card|
      ≤ ε + 5 / 2 * ∑ t ∈ univ.filter (fun t => ε ≤ |obsDev h k t|), law U (obs h k) t := by
  rw [← limAvg_devAvg hU h k]
  have hcomp := limAvg_comp hU (obs h k) (obsDev h k)
  have heq : (fun n => devAvg h k (blk (blockLen h k) n) (crtAt k (res (primeProd k) n)))
      = fun n => obsDev h k (obs h k n) := rfl
  rw [heq, hcomp]
  have hμ := law_nonneg hU (obs h k)
  have hμ1 := sum_law hU (obs h k)
  calc |∑ t, obsDev h k t * law U (obs h k) t|
      ≤ ∑ t, |obsDev h k t| * law U (obs h k) t := by
        refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun t _ => ?_))
        rw [abs_mul, abs_of_nonneg (hμ t)]
    _ = ∑ t ∈ univ.filter (fun t => ε ≤ |obsDev h k t|), |obsDev h k t| * law U (obs h k) t
        + ∑ t ∈ univ.filter (fun t => ¬ ε ≤ |obsDev h k t|), |obsDev h k t| * law U (obs h k) t :=
        (sum_filter_add_sum_filter_not _ _ _).symm
    _ ≤ ∑ t ∈ univ.filter (fun t => ε ≤ |obsDev h k t|), 5 / 2 * law U (obs h k) t
        + ∑ t ∈ univ.filter (fun t => ¬ ε ≤ |obsDev h k t|), ε * law U (obs h k) t := by
        refine add_le_add (sum_le_sum fun t _ => ?_) (sum_le_sum fun t ht => ?_)
        · exact mul_le_mul_of_nonneg_right (abs_devAvg_le h k _ _) (hμ t)
        · exact mul_le_mul_of_nonneg_right (not_le.mp (mem_filter.mp ht).2).le (hμ t)
    _ ≤ 5 / 2 * ∑ t ∈ univ.filter (fun t => ε ≤ |obsDev h k t|), law U (obs h k) t + ε * 1 := by
        rw [← mul_sum, ← mul_sum]
        refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hε)
        rw [← hμ1]
        exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun t _ _ => hμ t
    _ = _ := by ring

/-- **The mass of the deviation event.** `μ(A)(2ε²|𝐏_k|/25 − log 2) ≤ I_k + log 2`. -/
theorem mass_mul_le (hU : (U : Filter ℝ) ≤ atTop) (h k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    (∑ t ∈ univ.filter (fun t => ε ≤ |obsDev h k t|), law U (obs h k) t)
        * (2 * ε ^ 2 * (primesAt k).card / 25 - log 2)
      ≤ mutInf U (blockLen h k) (earlierProd k) (primeProd k) + log 2 := by
  set δ : ℝ := 2 * exp (-(2 * ε ^ 2 * (primesAt k).card / 25)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hsec : ∀ x : (Fin (blockLen h k) → Bool) × ZMod (earlierProd k),
      ((univ.filter fun y : ZMod (primeProd k) => ε ≤ |obsDev h k (x, y)|).card : ℝ)
        ≤ δ * Fintype.card (ZMod (primeProd k)) := by
    intro x
    rw [ZMod.card]
    exact card_devAvg_ge_le h k hε x.1
  have hev := mass_mul_neg_log_le (law_nonneg hU (obs h k)) (sum_law hU (obs h k))
    (fun t => ε ≤ |obsDev h k t|) hδ0 hsec
  have hlogδ : -log δ = 2 * ε ^ 2 * (primesAt k).card / 25 - log 2 := by
    rw [hδ, log_mul (by norm_num) (exp_pos _).ne', log_exp]
    ring
  have hfst : ent (push Prod.fst (law U (obs h k)))
      = entU U (fun n => (blk (blockLen h k) n, res (earlierProd k) n)) := by
    rw [← law_comp_eq_push hU (obs h k) Prod.fst]
    rfl
  have hjoint : ent (law U (obs h k))
      = entU U (fun n => (blk (blockLen h k) n, res (earlierProd k) n, res (primeProd k) n)) := by
    have := entU_comp_equiv hU (obs h k) (Equiv.prodAssoc _ _ _)
    show entU U (obs h k) = _
    rw [← this]
    rfl
  rw [hlogδ, hfst, hjoint, ZMod.card] at hev
  rw [mutInf]
  linarith

/-- **One good scale.** If `|𝐏_k| > C ≥ 25 log 2/ε³` and `I_k ≤ (ε³/25)|𝐏_k|`, then
`|c(h) − avg_{p∈𝐏_k} c(ph)| ≤ 6ε`. -/
theorem abs_corr_sub_le_of_good (hU : (U : Filter ℝ) ≤ atTop) (h k : ℕ) {ε C : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hC : 25 * log 2 ≤ ε ^ 3 * C) (hcard : C < (primesAt k).card)
    (hI : mutInf U (blockLen h k) (earlierProd k) (primeProd k)
      ≤ ε ^ 3 / 25 * (primesAt k).card) :
    |corr U h - (∑ p : primesAt k, corr U ((p : ℕ) * h)) / (primesAt k).card| ≤ 6 * ε := by
  set m := ∑ t ∈ univ.filter (fun t => ε ≤ |obsDev h k t|), law U (obs h k) t with hm
  set c : ℝ := ((primesAt k).card : ℝ) with hcdef
  have hm0 : 0 ≤ m := sum_nonneg fun t _ => law_nonneg hU _ t
  have hmass := mass_mul_le hU h k hε.le
  rw [← hm] at hmass
  have hε3 : ε ^ 3 ≤ ε ^ 2 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
  have hc0 : 0 < c := lt_of_le_of_lt (by
    have : 0 ≤ ε ^ 3 * C := le_trans (by positivity) hC
    exact (nonneg_of_mul_nonneg_right this (by positivity) : 0 ≤ C)) hcard
  have hlog : log 2 ≤ ε ^ 3 * c / 25 := by
    have : ε ^ 3 * C ≤ ε ^ 3 * c := mul_le_mul_of_nonneg_left hcard.le (by positivity)
    linarith
  have hlog' : log 2 ≤ ε ^ 2 * c / 25 := by
    have : ε ^ 3 * c ≤ ε ^ 2 * c := mul_le_mul_of_nonneg_right hε3 hc0.le
    linarith
  have hm2 : m ≤ 2 * ε := by
    have h1 : m * (ε ^ 2 * c / 25) ≤ m * (2 * ε ^ 2 * c / 25 - log 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hm0
    have h2 : m * (ε ^ 2 * c / 25) ≤ 2 * ε ^ 3 * c / 25 := by linarith
    have hpos : 0 < ε ^ 2 * c / 25 := by positivity
    rw [← le_div_iff₀ hpos] at h2
    calc m ≤ 2 * ε ^ 3 * c / 25 / (ε ^ 2 * c / 25) := h2
      _ = 2 * ε := by field_simp
  have := abs_corr_sub_le hU h k hε.le
  rw [← hm] at this
  linarith

/-! ## Infinitely many good scales -/

theorem primesAt_disjoint {j k : ℕ} (hjk : j ≠ k) : Disjoint (primesAt j) (primesAt k) := by
  rw [Finset.disjoint_left]
  intro p hpj hpk
  have h1 := lt_of_mem_primesAt hpj
  have h2 := le_of_mem_primesAt hpj
  have h3 := lt_of_mem_primesAt hpk
  have h4 := le_of_mem_primesAt hpk
  rcases lt_or_gt_of_ne hjk with h | h
  · have : 2 ^ (j + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
    omega
  · have : 2 ^ (k + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) h
    omega

/-- A prime `p ≤ 2^K` lies in `𝐏_k` for some `k < K`. -/
theorem exists_mem_primesAt {p K : ℕ} (hp : p.Prime) (hpK : p ≤ 2 ^ K) :
    ∃ k < K, p ∈ primesAt k := by
  have hp1 : p - 1 ≠ 0 := by have := hp.two_le; omega
  refine ⟨Nat.log 2 (p - 1), Nat.log_lt_of_lt_pow hp1 (by omega), mem_filter.mpr ⟨?_, hp⟩⟩
  have h1 := Nat.pow_log_le_self 2 hp1
  have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (p - 1)
  rw [mem_Ioc]
  constructor <;> omega

/-- `Σ_{k<K} Σ_{p∈𝐏_k} 1/p` is unbounded. -/
theorem exists_sum_recip_primesAt_gt (B : ℝ) :
    ∃ K, B < ∑ k ∈ range K, ∑ p ∈ primesAt k, (1 : ℝ) / p := by
  by_contra hcon
  push Not at hcon
  apply Nat.Primes.not_summable_one_div
  refine summable_of_sum_le (c := B) (fun p => by positivity) fun u => ?_
  obtain ⟨K, hK⟩ : ∃ K, ∀ p ∈ u, (p : ℕ) ≤ 2 ^ K := by
    refine ⟨u.sup (fun p => (p : ℕ)), fun p hp => ?_⟩
    exact (le_sup (f := fun p : Nat.Primes => (p : ℕ)) hp).trans
      (Nat.lt_two_pow_self).le
  refine le_trans ?_ (hcon K)
  rw [← sum_biUnion (fun j _ k _ hjk => primesAt_disjoint hjk)]
  have hsub : u.map ⟨fun p : Nat.Primes => (p : ℕ), fun a b h => Subtype.ext h⟩
      ⊆ (range K).biUnion primesAt := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := mem_map.mp hq
    obtain ⟨k, hk, hpk⟩ := exists_mem_primesAt p.2 (hK p hp)
    exact mem_biUnion.mpr ⟨k, mem_range.mpr hk, hpk⟩
  calc ∑ p ∈ u, 1 / ((p : ℕ) : ℝ)
      = ∑ q ∈ u.map ⟨fun p : Nat.Primes => (p : ℕ), fun a b h => Subtype.ext h⟩, 1 / (q : ℝ) := by
        rw [sum_map]
        rfl
    _ ≤ ∑ q ∈ (range K).biUnion primesAt, 1 / (q : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity

/-- The weights `w_k = (|𝐏_k| − C)₊/H_k` have divergent sums over `[K, ∞)`. -/
theorem exists_sum_weights_gt (h : ℕ) (C : ℝ) (K : ℕ) (B : ℝ) :
    ∃ K', K ≤ K' ∧ B < ∑ k ∈ Ico K K', max ((primesAt k).card - C) 0 / blockLen h k := by
  set a : ℝ := 2 * (h + 2) with ha
  have ha0 : 0 < a := by positivity
  obtain ⟨K', hK'⟩ := exists_sum_recip_primesAt_gt
    (a * (B + |C|) + ∑ k ∈ range K, ∑ p ∈ primesAt k, (1 : ℝ) / p)
  refine ⟨max K K', le_max_left _ _, ?_⟩
  set L := max K K' with hL
  have hKL : K ≤ L := le_max_left _ _
  -- dyadic comparison: `Σ_{p∈𝐏_k} 1/p ≤ a |𝐏_k|/H_k`
  have hrecip : ∀ k, ∑ p ∈ primesAt k, (1 : ℝ) / p ≤ a * ((primesAt k).card / blockLen h k) := by
    intro k
    have hH : (blockLen h k : ℝ) = 2 ^ k * a := by
      simp only [blockLen, ha]
      push_cast
      ring
    calc ∑ p ∈ primesAt k, (1 : ℝ) / p ≤ ∑ _p ∈ primesAt k, (1 : ℝ) / 2 ^ k := by
          refine sum_le_sum fun p hp => ?_
          have : (2 : ℝ) ^ k < p := by exact_mod_cast lt_of_mem_primesAt hp
          exact div_le_div_of_nonneg_left zero_le_one (by positivity) this.le
      _ = a * ((primesAt k).card / blockLen h k) := by
          rw [sum_const, nsmul_eq_mul, hH]
          field_simp
  -- the subtracted part is a convergent geometric sum
  have hgeom : ∑ k ∈ Ico K L, C / blockLen h k ≤ |C| := by
    calc ∑ k ∈ Ico K L, C / blockLen h k ≤ ∑ k ∈ Ico K L, |C| * (1 / 2) ^ (k + 1) := by
          refine sum_le_sum fun k _ => ?_
          have hH : (blockLen h k : ℝ) = 2 ^ (k + 1) * (h + 2) := by
            simp only [blockLen]
            push_cast
            ring
          rw [hH, one_div_pow, ← div_eq_mul_one_div]
          calc C / (2 ^ (k + 1) * (h + 2)) ≤ |C| / (2 ^ (k + 1) * (h + 2)) :=
                div_le_div_of_nonneg_right (le_abs_self C) (by positivity)
            _ ≤ |C| / 2 ^ (k + 1) :=
                div_le_div_of_nonneg_left (abs_nonneg C) (by positivity)
                  (le_mul_of_one_le_right (by positivity) (by linarith [(Nat.cast_nonneg h : (0:ℝ) ≤ h)]))
      _ ≤ ∑ k ∈ range L, |C| * (1 / 2) ^ (k + 1) :=
          sum_le_sum_of_subset_of_nonneg (fun k hk => mem_range.mpr (mem_Ico.mp hk).2)
            fun _ _ _ => by positivity
      _ = |C| * ((1 / 2) * ∑ k ∈ range L, (1 / 2 : ℝ) ^ k) := by
          rw [mul_sum, mul_sum]
          refine sum_congr rfl fun k _ => ?_
          ring
      _ ≤ |C| * ((1 / 2) * 2) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by norm_num))
            (abs_nonneg C)
          exact sum_geometric_two_le L
      _ = |C| := by ring
  have hsplit : ∑ k ∈ range L, ∑ p ∈ primesAt k, (1 : ℝ) / p
      = ∑ k ∈ range K, ∑ p ∈ primesAt k, (1 : ℝ) / p
        + ∑ k ∈ Ico K L, ∑ p ∈ primesAt k, (1 : ℝ) / p :=
    (sum_range_add_sum_Ico _ hKL).symm
  have hmono : ∑ k ∈ range K', ∑ p ∈ primesAt k, (1 : ℝ) / p
      ≤ ∑ k ∈ range L, ∑ p ∈ primesAt k, (1 : ℝ) / p :=
    sum_le_sum_of_subset_of_nonneg (range_mono (le_max_right _ _))
      fun _ _ _ => sum_nonneg fun _ _ => by positivity
  have hlow : ∑ k ∈ Ico K L, ∑ p ∈ primesAt k, (1 : ℝ) / p
      ≤ a * ∑ k ∈ Ico K L, max ((primesAt k).card - C) 0 / blockLen h k + a * |C| := by
    calc ∑ k ∈ Ico K L, ∑ p ∈ primesAt k, (1 : ℝ) / p
        ≤ ∑ k ∈ Ico K L, a * ((primesAt k).card / blockLen h k) := sum_le_sum fun k _ => hrecip k
      _ = a * (∑ k ∈ Ico K L, ((primesAt k).card - C) / blockLen h k
            + ∑ k ∈ Ico K L, C / blockLen h k) := by
          rw [← sum_add_distrib, mul_sum]
          refine sum_congr rfl fun k _ => ?_
          ring
      _ ≤ a * (∑ k ∈ Ico K L, max ((primesAt k).card - C) 0 / blockLen h k + |C|) := by
          refine mul_le_mul_of_nonneg_left (add_le_add (sum_le_sum fun k _ => ?_) hgeom) ha0.le
          exact div_le_div_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
      _ = _ := by ring
  nlinarith

/-- **Infinitely many scales of near self-similarity.** For `0 < ε ≤ 1` and every `K` there is a
scale `k ≥ K` with `|c(h) − avg_{p∈𝐏_k} c(ph)| ≤ 6ε`. -/
theorem exists_scale_corr_close (hU : (U : Filter ℝ) ≤ atTop) (h : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (K : ℕ) :
    ∃ k, K ≤ k ∧
      |corr U h - (∑ p : primesAt k, corr U ((p : ℕ) * h)) / (primesAt k).card| ≤ 6 * ε := by
  set C : ℝ := 25 * log 2 / ε ^ 3 with hCdef
  have hC : 25 * log 2 ≤ ε ^ 3 * C := by
    rw [hCdef]
    field_simp
    exact le_rfl
  set δ : ℝ := ε ^ 3 / 25 with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨K', hKK', hK'⟩ := exists_sum_weights_gt h C K (log 2 / δ)
  have hlog : log 2 < δ * ∑ k ∈ Ico K K', max ((primesAt k).card - C) 0 / blockLen h k := by
    rw [div_lt_iff₀ hδ0] at hK'
    linarith
  obtain ⟨k, hk, hwpos, hgood⟩ := exists_good_scale_weighted hU (blockLen h) earlierProd primeProd
    (blockLen_pos h) (blockLen_succ h) earlierProd_succ coprime_earlierProd_primeProd
    (fun k => max ((primesAt k).card - C) 0 / blockLen h k)
    (fun k => div_nonneg (le_max_right _ _) (Nat.cast_nonneg _)) hlog
  have hH : (0 : ℝ) < blockLen h k := by exact_mod_cast blockLen_pos h k
  have hcard : C < (primesAt k).card := by
    by_contra hle
    push Not at hle
    have : max ((primesAt k).card - C) 0 = 0 := max_eq_right (by linarith)
    rw [this, zero_div] at hwpos
    exact lt_irrefl 0 hwpos
  have hC0 : 0 ≤ C := by positivity
  have hI : mutInf U (blockLen h k) (earlierProd k) (primeProd k)
      ≤ ε ^ 3 / 25 * (primesAt k).card := by
    rw [max_eq_left (by linarith)] at hgood
    have h1 := (div_le_iff₀ hH).mp hgood
    have h2 : δ * (((primesAt k).card - C) / blockLen h k) * blockLen h k
        = δ * ((primesAt k).card - C) := by
      field_simp
    rw [h2] at h1
    have h3 : δ * ((primesAt k).card - C) ≤ δ * (primesAt k).card :=
      mul_le_mul_of_nonneg_left (by linarith) hδ0.le
    rw [← hδ]
    linarith
  exact ⟨k, (mem_Ico.mp hk).1, abs_corr_sub_le_of_good hU h k hε hε1 hC hcard hI⟩

end

end GaloisForLFunctions.LogarithmicChowla
