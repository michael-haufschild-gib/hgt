import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheRamanujanTwinsCarryThePrimes

/-!
# The twisted entries are digamma sums

Write `G(z) = Σ_k (1/(k + z) − 1/(k + 1)) = −ψ(z) − γ` for the renormalized lattice germ. For a
`q`-periodic `p` with mean `μ` and `b = p − μ`, the renormalized periodic germ has the closed form

`lim_{r→1⁻} (Σ_k r^k p(k)/(k + w) + μ log(1 − r)) = μ G(w) + (1/q) Σ_{j<q} b(j) G((j + w)/q)`

(`tendsto_twistedGerm_add_mean_log_eq`): grouping the mean-zero part over full periods turns
`Σ_k b(k)/(k + w)` into `(1/q) Σ_j b(j) Σ_l (1/(l + (j + w)/q) − 1/(l + 1))`.

* Every entry of every periodic germ family — in particular of the Ramanujan twins — is a finite
  combination of digamma values at rational shifts of the nodes (`periodicGerm_limit_eq`).
* At the pole nodes of two different torsion orders the entry is `−I(m, n)`, so
  **the orbit intersections are digamma sums** (`orbitIntersection_eq_digamma_sum`):
  `I(m, n) = −(1/q) Σ_{j<q} c_m(j + 1) c_n(j + 1) G((j + 1)/q)` for `m ≠ n` and `m, n ∣ q`;
  with `I(m, mt) = φ(m)Λ(t)` this writes the von Mangoldt function through `ψ` at rationals.

So the survival inequality of the twins is explicit: its pole-node block is the prime kernel and its
other entries are digamma values at rational points.
-/

noncomputable section

open Filter Topology Finset

namespace GaloisForLFunctions.RenormalizedBiarithmeticGeometry

open ArithmeticEffectivityTheory

/-- The renormalized lattice germ at `z > 0` is the limit of its partial sums. -/
theorem tendsto_partial_latticeGermLimit {z : ℝ} (hz : 0 < z) :
    Tendsto (fun n => ∑ l ∈ range n, (1 / ((l : ℝ) + z) - 1 / ((l : ℝ) + 1))) atTop
      (𝓝 (latticeGermLimit z)) :=
  ((summable_abs_latticeGermLimit hz).of_abs.hasSum).tendsto_sum_nat

/-- Sums over `n` full periods regroup into `n` blocks. -/
theorem sum_range_mul_eq (g : ℕ → ℝ) (q n : ℕ) :
    ∑ k ∈ range (n * q), g k = ∑ l ∈ range n, ∑ j ∈ range q, g (l * q + j) := by
  induction n with
  | zero => simp
  | succ n ih => rw [show (n + 1) * q = n * q + q by ring, sum_range_add, ih, Finset.sum_range_succ]

/-- **Closed form of the renormalized periodic germ.** -/
theorem tendsto_twistedGerm_add_mean_log_eq {p : ℕ → ℝ} {q : ℕ} (hq : 0 < q)
    (hper : Function.Periodic p q) {w : ℝ} (hw : 0 < w) :
    Tendsto (fun r => twistedGerm p r w + periodMean p q * Real.log (1 - r)) (𝓝[<] 1)
      (𝓝 (periodMean p q * latticeGermLimit w +
        (1 / q) * ∑ j ∈ range q, (p j - periodMean p q) * latticeGermLimit ((j + w) / q))) := by
  set μ := periodMean p q
  set b : ℕ → ℝ := fun k => p k - μ
  have hbper : Function.Periodic b q := fun k => by simp only [b, hper k]
  have hbzero : ∑ i ∈ range q, b i = 0 := by
    simp only [b, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, μ, periodMean]
    field_simp
    ring
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  -- Dirichlet's test: the partial sums of `b(k)/(k + w)` converge to some `l`.
  have hanti : Antitone fun k : ℕ => 1 / ((k : ℝ) + w) := fun i j hij => by
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hzero : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + w)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ w tendsto_natCast_atTop_atTop)
  have hcs := hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hzero
    (b := ∑ i ∈ range q, |b i|) (z := b) fun n => by
      rw [Real.norm_eq_abs]; exact abs_sum_range_le_of_periodic hq hbper hbzero n
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcs
  -- Along full periods the partial sums are digamma sums.
  set R : ℝ := (1 / q) * ∑ j ∈ range q, b j * latticeGermLimit ((j + w) / q)
  have hbj : ∀ j l : ℕ, b (l * q + j) = b j := fun j l => by
    rw [add_comm]; exact (hbper.nat_mul l) j
  have hblock : ∀ n, ∑ k ∈ range (n * q), 1 / ((k : ℝ) + w) * b k =
      (1 / q) * ∑ j ∈ range q, b j *
        ∑ l ∈ range n, (1 / ((l : ℝ) + (j + w) / q) - 1 / ((l : ℝ) + 1)) := by
    intro n
    have hL : ∑ k ∈ range (n * q), 1 / ((k : ℝ) + w) * b k =
        ∑ j ∈ range q, ∑ l ∈ range n, b j * (1 / ((l : ℝ) * q + j + w)) := by
      rw [sum_range_mul_eq, sum_comm]
      refine sum_congr rfl fun j _ => sum_congr rfl fun l _ => ?_
      rw [hbj j l]
      push_cast
      ring
    have hR : (1 / q) * ∑ j ∈ range q, b j *
        ∑ l ∈ range n, (1 / ((l : ℝ) + (j + w) / q) - 1 / ((l : ℝ) + 1)) =
          ∑ j ∈ range q, ∑ l ∈ range n, b j * (1 / ((l : ℝ) * q + j + w)) -
            ∑ j ∈ range q, ∑ l ∈ range n, b j * (1 / (q * ((l : ℝ) + 1))) := by
      rw [mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun j _ => ?_
      rw [mul_sum, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun l _ => ?_
      have h1 : (0 : ℝ) < (l : ℝ) * q + j + w := by positivity
      have h2 : (0 : ℝ) < (l : ℝ) + 1 := by positivity
      field_simp
      ring
    have hZ : ∑ j ∈ range q, ∑ l ∈ range n, b j * (1 / (q * ((l : ℝ) + 1))) = 0 := by
      rw [sum_comm]
      exact sum_eq_zero fun l _ => by rw [← sum_mul, hbzero, zero_mul]
    rw [hL, hR, hZ, sub_zero]
  have hRlim : Tendsto (fun n => (1 / q) * ∑ j ∈ range q, b j *
      ∑ l ∈ range n, (1 / ((l : ℝ) + (j + w) / q) - 1 / ((l : ℝ) + 1))) atTop (𝓝 R) :=
    (tendsto_finsetSum _ fun j _ =>
      (tendsto_partial_latticeGermLimit (by positivity)).const_mul (b j)).const_mul
        ((1 : ℝ) / q)
  have hmul : Tendsto (fun n : ℕ => n * q) atTop atTop :=
    tendsto_atTop_atTop.mpr fun c => ⟨c, fun n hn => hn.trans (Nat.le_mul_of_pos_right n hq)⟩
  have hlR : l = R := by
    have h1 : Tendsto (fun n => ∑ k ∈ range (n * q), 1 / ((k : ℝ) + w) * b k) atTop (𝓝 l) := by
      have := hl.comp hmul
      simpa only [Function.comp_def, smul_eq_mul] using this
    exact tendsto_nhds_unique h1 (hRlim.congr fun n => (hblock n).symm)
  -- Abel's theorem and the lattice germ, as for the existence statement.
  have hAbel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt
    (f := fun k : ℕ => 1 / ((k : ℝ) + w) * b k) (l := l) (by simpa only [smul_eq_mul] using hl)
  have hlat := (tendsto_latticeGerm_add_log hw).const_mul μ
  have hgoal : μ * latticeGermLimit w + (1 / q) * ∑ j ∈ range q, (p j - μ) *
      latticeGermLimit ((j + w) / q) = μ * latticeGermLimit w + l := by rw [hlR]
  rw [hgoal]
  refine (hlat.add hAbel).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  have hbB : ∀ k, |b k| ≤ ∑ i ∈ range q, |b i| := abs_le_of_periodic hq hbper
  have hs1 := (hasSum_latticeGerm hr.1.le hr.2 hw).mul_left μ
  have hs2 := (summable_twistedGerm hbB hr.1.le hr.2 hw).hasSum
  have hsum := hs1.add hs2
  have heq : twistedGerm p r w = μ * latticeGerm r w +
      ∑' k : ℕ, r ^ k * b k / ((k : ℝ) + w) := by
    rw [twistedGerm, ← hsum.tsum_eq]
    refine tsum_congr fun k => ?_
    simp only [b]
    ring
  have hpow : ∑' k : ℕ, r ^ k * b k / ((k : ℝ) + w) =
      ∑' k : ℕ, 1 / ((k : ℝ) + w) * b k * r ^ k := tsum_congr fun k => by ring
  rw [heq, hpow]
  ring

/-- **The entries of every periodic germ family are digamma sums.** -/
theorem periodicGerm_limit_eq {n : ℕ} (a : Fin n → ℕ → ℝ) {q : ℕ} (hq : 0 < q)
    (hper : ∀ α, Function.Periodic (a α) q) {x : Fin n → ℝ} (hx : ∀ α, 0 ≤ x α) (α β : Fin n) :
    Tendsto (fun r => periodicGerm a x r α β - (-Real.log (1 - r)) * cesaroGram a q α β)
      (𝓝[<] 1) (𝓝 (cesaroGram a q α β * latticeGermLimit (1 + x α + x β) +
        (1 / q) * ∑ j ∈ range q, (a α j * a β j - cesaroGram a q α β) *
          latticeGermLimit ((j + (1 + x α + x β)) / q))) := by
  have hprod : Function.Periodic (fun k => a α k * a β k) q := fun k => by
    simp only [hper α k, hper β k]
  refine (tendsto_twistedGerm_add_mean_log_eq hq hprod
    (show 0 < 1 + x α + x β by linarith [hx α, hx β])).congr fun r => ?_
  simp only [periodicGerm, cesaroGram, Matrix.of_apply]
  ring

/-- **The orbit intersections are digamma sums.** For distinct positive orders `m, n` dividing
`q`, `I(m, n) = −(1/q) Σ_{j<q} c_m(j+1) c_n(j+1) G((j + 1)/q)`. -/
theorem orbitIntersection_eq_digamma_sum {m n q : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n)
    (hq : 0 < q) (hmq : m ∣ q) (hnq : n ∣ q) :
    orbitIntersection m n = -((1 / q) * ∑ j ∈ range q,
      shiftedMode m j * shiftedMode n j * latticeGermLimit ((j + 1) / q)) := by
  have hper : Function.Periodic (fun k => shiftedMode m k * shiftedMode n k) q := by
    have h1 := (shiftedMode_periodic hm).nat_mul (q / m)
    have h2 := (shiftedMode_periodic hn).nat_mul (q / n)
    rw [Nat.cast_id, Nat.div_mul_cancel hmq] at h1
    rw [Nat.cast_id, Nat.div_mul_cancel hnq] at h2
    exact h1.mul h2
  have hmean : periodMean (fun k => shiftedMode m k * shiftedMode n k) q = 0 := by
    simp only [periodMean]
    rw [sum_shiftedMode_mul hm hn hmq hnq, if_neg hmn, zero_div]
  have h1 := tendsto_twistedGerm_add_mean_log_eq hq hper one_pos
  rw [hmean] at h1
  simp only [zero_mul, add_zero, zero_add, sub_zero] at h1
  have h2 := tendsto_twin_poleNode hm hn hmn
  have := tendsto_nhds_unique h2 h1
  rw [neg_eq_iff_eq_neg] at this
  rw [this]

/-- **Von Mangoldt as a digamma sum.** For `m ≥ 1`, `t > 1` and `q = m · mt`:
`φ(m)Λ(t) = −(1/q) Σ_{j<q} c_m(j+1) c_{mt}(j+1) G((j + 1)/q)`. -/
theorem totient_mul_vonMangoldt_eq_digamma_sum {m t : ℕ} (hm : 0 < m) (ht : 1 < t) :
    (Nat.totient m : ℝ) * ArithmeticFunction.vonMangoldt t =
      -((1 / (m * (m * t) : ℕ)) * ∑ j ∈ range (m * (m * t)),
        shiftedMode m j * shiftedMode (m * t) j * latticeGermLimit ((j + 1) / (m * (m * t) : ℕ))) := by
  have hmt : 0 < m * t := Nat.mul_pos hm (by omega)
  have hne : m ≠ m * t := by
    intro h
    have h1 : m * 1 = m * t := by rw [mul_one]; exact h
    have := Nat.eq_of_mul_eq_mul_left hm h1
    omega
  rw [← orbitIntersection_hecke hm ht]
  exact orbitIntersection_eq_digamma_sum hm hmt hne (Nat.mul_pos hm hmt) (dvd_mul_right m _)
    (dvd_mul_left _ _)

end GaloisForLFunctions.RenormalizedBiarithmeticGeometry
