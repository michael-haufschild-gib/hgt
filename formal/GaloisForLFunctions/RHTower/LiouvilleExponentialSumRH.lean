import GaloisForLFunctions.RHTower.LiouvilleSummatoryRH

/-!
# The exponential Liouville sum under RH

`J(t) = Σ λ(n) e^{-nt}/n` satisfies `J(t) = O(t^{½-ε})` as `t → 0⁺` for every `ε > 0` if and only if
the Riemann hypothesis holds (`riemannHypothesis_iff_forall_liouvilleExpSum_isBigO`).

**Proof of `RH ⇒ J = O(t^{½-ε})`.**
* Under RH, `L(N) = Σ_{n ≤ N} λ(n) = O(N^{½+δ})` (`LiouvilleSummatoryRH`).
* Abel summation against `e^{-nt}/n` and against `1/n` gives, for every `K`,
  `Σ_{n ≤ K} λ(n) e^{-nt}/n = Σ_{n ≤ K} λ(n)/n + L(K)φ_t(K) + Σ_{n < K} L(n)(φ_t(n) − φ_t(n+1))`,
  `φ_t(x) = (e^{-xt} − 1)/x`.  Since `0 ≤ φ_t' (x) = (1 − (1 + xt)e^{-xt})/x² ≤ t^q x^{q-2}`,
  the last series converges absolutely to `D(t)` with `|D(t)| ≤ C t^q`, `q = ½ − 2δ`.  Hence
  `Σ_{n ≤ K} λ(n)/n` converges, to a constant `c₀`, and `J(t) = c₀ + D(t)`
  (`exists_liouvilleExpSum_sub_const_le`).
* `c₀ = 0` (`const_eq_zero_of_liouvilleExpSum_sub_const_le`): `J − c₀e^{-t}` is `O(t^q)` at `0`,
  so its Mellin transform is holomorphic at `0`; on `Re s > 0` it equals the Liouville kernel minus
  `c₀Γ(s)`, the kernel is finite at `0`, and `sΓ(s) → 1`.

The converse is `riemannHypothesis_of_forall_liouvilleExpSum_isBigO`.  The Abel step uses only the
summatory bound, so `RH ⟺ ∀δ>0, L(N) = O(N^{½+δ})` as well
(`riemannHypothesis_iff_forall_liouvilleSummatory_le`).
-/

open Complex Filter Topology MeasureTheory Set Asymptotics

namespace RHTower

noncomputable section

/-! ## Summation by parts -/

/-- **Abel summation.**  `Σ_{n ≤ K} a_n b_n = A(K)b(K) + Σ_{1 ≤ n < K} A(n)(b(n) − b(n+1))`,
`A = sourcePartialSum a`. -/
theorem sum_Icc_mul_eq_abel (a b : ℕ → ℝ) (K : ℕ) :
    ∑ n ∈ Finset.Icc 1 K, a n * b n = sourcePartialSum a K * b K +
      ∑ n ∈ Finset.Ico 1 K, sourcePartialSum a n * (b n - b (n + 1)) := by
  induction K with
  | zero => simp [sourcePartialSum]
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp [sourcePartialSum]
    · rw [Finset.sum_Ico_succ_top (by omega)]
      have hA : sourcePartialSum a (K + 1) = sourcePartialSum a K + a (K + 1) := by
        rw [sourcePartialSum, sourcePartialSum, Finset.sum_Icc_succ_top (by omega)]
      rw [hA]; ring

/-! ## The comparison function `φ_t(x) = (e^{-xt} − 1)/x` -/

/-- `φ_t(x) = (e^{-xt} − 1)/x`. -/
def liouvilleAbelPhi (t x : ℝ) : ℝ := (Real.exp (-(x * t)) - 1) / x

theorem hasDerivAt_liouvilleAbelPhi (t : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (liouvilleAbelPhi t) ((1 - (1 + x * t) * Real.exp (-(x * t))) / x ^ 2) x := by
  have h1 : HasDerivAt (fun y => Real.exp (-(y * t)) - 1) (Real.exp (-(x * t)) * (-t)) x := by
    have := (((hasDerivAt_id' x).mul_const t).neg).exp
    simpa using this.sub_const 1
  refine (h1.div (hasDerivAt_id' x) hx).congr_deriv ?_
  field_simp
  ring

/-- `0 ≤ 1 − (1 + u)e^{-u} ≤ u^q` for `u ≥ 0` and `0 < q ≤ 2`. -/
theorem one_sub_one_add_mul_exp_neg_le {u q : ℝ} (hu : 0 ≤ u) (hq : 0 < q) (hq2 : q ≤ 2) :
    0 ≤ 1 - (1 + u) * Real.exp (-u) ∧ 1 - (1 + u) * Real.exp (-u) ≤ u ^ q := by
  have he : 0 < Real.exp (-u) := Real.exp_pos _
  have h1 : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hinv : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have h2 : 1 - u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
  refine ⟨?_, ?_⟩
  · nlinarith
  · rcases le_total u 1 with hu1 | hu1
    · have hsq : 1 - (1 + u) * Real.exp (-u) ≤ u ^ 2 := by nlinarith
      have : u ^ (2 : ℝ) ≤ u ^ q := by
        rcases eq_or_lt_of_le hu with rfl | hu0
        · rw [Real.zero_rpow (by norm_num), Real.zero_rpow hq.ne']
        · exact Real.rpow_le_rpow_of_exponent_ge hu0 hu1 hq2
      rw [Real.rpow_two] at this
      linarith
    · have : 1 ≤ u ^ q := Real.one_le_rpow hu1 hq.le
      nlinarith

/-- **The comparison increments.**  For `t > 0`, `n ≥ 1` and `0 < q ≤ 2`,
`|φ_t(n) − φ_t(n+1)| ≤ t^q n^{q-2}`. -/
theorem abs_liouvilleAbelPhi_sub_le {t q : ℝ} (ht : 0 < t) (hq : 0 < q) (hq2 : q ≤ 2) {n : ℕ}
    (hn : 1 ≤ n) :
    |liouvilleAbelPhi t n - liouvilleAbelPhi t (n + 1)| ≤ t ^ q * (n : ℝ) ^ (q - 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hderiv : ∀ x ∈ uIcc (n : ℝ) (n + 1), HasDerivAt (liouvilleAbelPhi t)
      ((1 - (1 + x * t) * Real.exp (-(x * t))) / x ^ 2) x := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact hasDerivAt_liouvilleAbelPhi t (by linarith [hx.1])
  have hcont : ContinuousOn (fun x : ℝ => (1 - (1 + x * t) * Real.exp (-(x * t))) / x ^ 2)
      (uIcc (n : ℝ) (n + 1)) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
    rw [uIcc_of_le (by linarith)] at hx
    exact pow_ne_zero 2 (by linarith [hx.1])
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  have hbound : ∀ x ∈ Set.uIoc (n : ℝ) (n + 1),
      ‖(1 - (1 + x * t) * Real.exp (-(x * t))) / x ^ 2‖ ≤ t ^ q * (n : ℝ) ^ (q - 2) := by
    intro x hx
    rw [uIoc_of_le (by linarith)] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hu : 0 ≤ x * t := by positivity
    obtain ⟨h0, h1⟩ := one_sub_one_add_mul_exp_neg_le hu hq hq2
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg h0 (by positivity)),
      div_le_iff₀ (by positivity)]
    have e : (x * t) ^ q = t ^ q * x ^ q := by
      rw [Real.mul_rpow hx0.le ht.le]; ring
    have hxq : x ^ (q - 2) ≤ (n : ℝ) ^ (q - 2) :=
      Real.rpow_le_rpow_of_nonpos hn0 hx.1.le (by linarith)
    have e2 : x ^ q = x ^ (q - 2) * x ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hx0]; norm_num
    calc 1 - (1 + x * t) * Real.exp (-(x * t)) ≤ (x * t) ^ q := h1
      _ = t ^ q * x ^ (q - 2) * x ^ 2 := by rw [e, e2]; ring
      _ ≤ t ^ q * (n : ℝ) ^ (q - 2) * x ^ 2 := by gcongr
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [hint, show (n : ℝ) + 1 - n = 1 by ring, abs_one, mul_one] at this
  rw [abs_sub_comm]
  exact this

/-! ## The decomposition `J(t) = c₀ + D(t)` -/

theorem liouvilleExpCoeff_mul_exp (n : ℕ) (t : ℝ) :
    liouvilleExpCoeff n * Real.exp (-(n * t)) = liouvilleR n * (Real.exp (-(n * t)) / n) := by
  rw [liouvilleExpCoeff, liouvilleR]; ring

theorem tendsto_sum_Icc_liouvilleExpSum {t : ℝ} (ht : 0 < t) :
    Tendsto (fun K : ℕ => ∑ n ∈ Finset.Icc 1 K, liouvilleR n * (Real.exp (-(n * t)) / n)) atTop
      (𝓝 (liouvilleExpSum t)) := by
  have h := ((summable_liouvilleExpTerm ht).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  refine h.congr fun K => ?_
  simp only [Function.comp_apply]
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  simp only [liouvilleExpCoeff, Nat.cast_zero, div_zero, zero_mul, zero_add]
  rw [show Finset.Ico 1 (K + 1) = Finset.Icc 1 K by ext; simp]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [liouvilleR]; ring

/-- **The decomposition.**  If `|L(N)| ≤ C(N+1)^{½+δ}` with `0 < δ < ¼`, there is a constant `c₀`
with `|J(t) − c₀| ≤ C' t^{½-2δ}` for all `t > 0`. -/
theorem exists_liouvilleExpSum_sub_const_le {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ < 1 / 4)
    (hL : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |sourcePartialSum liouvilleR N| ≤ C * ((N : ℝ) + 1) ^ (1 / 2 + δ)) :
    ∃ c₀ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → |liouvilleExpSum t - c₀| ≤ C * t ^ (1 / 2 - 2 * δ) := by
  obtain ⟨CL, hCL0, hCL⟩ := hL
  set p : ℝ := 1 / 2 + δ with hp
  set q : ℝ := 1 / 2 - 2 * δ with hq
  have hq0 : 0 < q := by rw [hq]; linarith
  have hq2 : q ≤ 2 := by rw [hq]; linarith
  set Lf : ℕ → ℝ := sourcePartialSum liouvilleR with hLf
  set d : ℝ → ℕ → ℝ := fun t n => Lf (n + 1) *
    (liouvilleAbelPhi t (n + 1 : ℕ) - liouvilleAbelPhi t (n + 1 + 1 : ℕ)) with hd
  have hZs : Summable fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ (1 + δ) :=
    (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_rpow.2 (by linarith))
  set Z := ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ (1 + δ) with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg fun n => by positivity
  have hdb : ∀ t : ℝ, 0 < t → ∀ n : ℕ,
      |d t n| ≤ CL * 2 ^ p * t ^ q * (1 / ((n + 1 : ℕ) : ℝ) ^ (1 + δ)) := by
    intro t ht n
    have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 1)
    have hL := hCL (n + 1)
    have hphi := abs_liouvilleAbelPhi_sub_le ht hq0 hq2 (n := n + 1) (by omega)
    rw [show ((n + 1 : ℕ) : ℝ) + 1 = ((n + 1 + 1 : ℕ) : ℝ) by push_cast; ring] at hphi
    have hL' : |Lf (n + 1)| ≤ CL * 2 ^ p * ((n + 1 : ℕ) : ℝ) ^ p := by
      refine le_trans hL ?_
      have h2 : ((n + 1 : ℕ) : ℝ) + 1 ≤ 2 * ((n + 1 : ℕ) : ℝ) := by linarith
      calc CL * (((n + 1 : ℕ) : ℝ) + 1) ^ p ≤ CL * (2 * ((n + 1 : ℕ) : ℝ)) ^ p :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) h2 (by positivity)) hCL0
        _ = CL * 2 ^ p * ((n + 1 : ℕ) : ℝ) ^ p := by
            rw [Real.mul_rpow (by norm_num) (by positivity)]; ring
    have hexp : ((n + 1 : ℕ) : ℝ) ^ p * ((n + 1 : ℕ) : ℝ) ^ (q - 2) =
        1 / ((n + 1 : ℕ) : ℝ) ^ (1 + δ) := by
      rw [← Real.rpow_add (by positivity), show p + (q - 2) = -(1 + δ) by rw [hp, hq]; ring,
        Real.rpow_neg (by positivity), one_div]
    rw [hd]; dsimp only
    rw [abs_mul]
    calc |Lf (n + 1)| * |liouvilleAbelPhi t ((n + 1 : ℕ) : ℝ) -
          liouvilleAbelPhi t ((n + 1 + 1 : ℕ) : ℝ)|
        ≤ (CL * 2 ^ p * ((n + 1 : ℕ) : ℝ) ^ p) * (t ^ q * ((n + 1 : ℕ) : ℝ) ^ (q - 2)) :=
          mul_le_mul hL' hphi (abs_nonneg _) (by positivity)
      _ = CL * 2 ^ p * t ^ q * (((n + 1 : ℕ) : ℝ) ^ p * ((n + 1 : ℕ) : ℝ) ^ (q - 2)) := by ring
      _ = _ := by rw [hexp]
  have hds : ∀ t : ℝ, 0 < t → Summable (d t) := fun t ht =>
    Summable.of_norm_bounded (hZs.mul_left (CL * 2 ^ p * t ^ q)) fun n => by
      rw [Real.norm_eq_abs]; exact hdb t ht n
  set D : ℝ → ℝ := fun t => ∑' n, d t n with hD
  have hDb : ∀ t : ℝ, 0 < t → |D t| ≤ CL * 2 ^ p * Z * t ^ q := by
    intro t ht
    have h1 := norm_tsum_le_tsum_norm (hds t ht).norm
    have h2 := Summable.tsum_le_tsum (fun n => by rw [Real.norm_eq_abs]; exact hdb t ht n)
      (hds t ht).norm (hZs.mul_left (CL * 2 ^ p * t ^ q))
    rw [tsum_mul_left] at h2
    rw [← Real.norm_eq_abs]
    calc ‖D t‖ ≤ CL * 2 ^ p * t ^ q * Z := h1.trans h2
      _ = CL * 2 ^ p * Z * t ^ q := by ring
  -- the boundary term `L(K)φ_t(K)` tends to `0`
  have hbdry : ∀ t : ℝ, 0 < t → Tendsto (fun K : ℕ => Lf K * liouvilleAbelPhi t K) atTop (𝓝 0) := by
    intro t ht
    have hpow : Tendsto (fun K : ℕ => CL * 2 ^ p * ((K : ℝ) ^ (-(1 / 2 - δ)))) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := 1 / 2 - δ) (by linarith)).comp
        tendsto_natCast_atTop_atTop
      simpa using this.const_mul (CL * 2 ^ p)
    refine squeeze_zero_norm' ?_ hpow
    filter_upwards [eventually_ge_atTop 1] with K hK
    have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
    have hφ : |liouvilleAbelPhi t K| ≤ 1 / K := by
      rw [liouvilleAbelPhi, abs_div, abs_of_pos hK0]
      refine div_le_div_of_nonneg_right ?_ hK0.le
      have h1 : 0 < Real.exp (-(K * t)) := Real.exp_pos _
      have h2 : Real.exp (-(K * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      rw [abs_le]; constructor <;> linarith
    have hL : |Lf K| ≤ CL * 2 ^ p * (K : ℝ) ^ p := by
      refine le_trans (hCL K) ?_
      have h2 : (K : ℝ) + 1 ≤ 2 * K := by
        have : (1 : ℝ) ≤ K := by exact_mod_cast hK
        linarith
      calc CL * ((K : ℝ) + 1) ^ p ≤ CL * (2 * (K : ℝ)) ^ p :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) h2 (by positivity)) hCL0
        _ = CL * 2 ^ p * (K : ℝ) ^ p := by rw [Real.mul_rpow (by norm_num) hK0.le]; ring
    rw [Real.norm_eq_abs, abs_mul]
    have e : (K : ℝ) ^ (-(1 / 2 - δ)) = (K : ℝ) ^ p * (1 / K) := by
      rw [show -(1 / 2 - δ) = p + (-1) by rw [hp]; ring, Real.rpow_add hK0, Real.rpow_neg_one,
        one_div]
    rw [e]
    calc |Lf K| * |liouvilleAbelPhi t K| ≤ (CL * 2 ^ p * (K : ℝ) ^ p) * (1 / K) :=
          mul_le_mul hL hφ (abs_nonneg _) (by positivity)
      _ = CL * 2 ^ p * ((K : ℝ) ^ p * (1 / K)) := by ring
  -- partial sums of `λ(n)/n`
  have hlim : ∀ t : ℝ, 0 < t → Tendsto (fun K : ℕ => ∑ n ∈ Finset.Icc 1 K, liouvilleR n * (1 / n))
      atTop (𝓝 (liouvilleExpSum t - D t)) := by
    intro t ht
    have hid : ∀ K : ℕ, 1 ≤ K → ∑ n ∈ Finset.Icc 1 K, liouvilleR n * (1 / n) =
        ∑ n ∈ Finset.Icc 1 K, liouvilleR n * (Real.exp (-(n * t)) / n) -
          (Lf K * liouvilleAbelPhi t K + ∑ m ∈ Finset.range (K - 1), d t m) := by
      intro K hK
      have habel := sum_Icc_mul_eq_abel liouvilleR (fun n => liouvilleAbelPhi t n) K
      have hsplit : ∑ n ∈ Finset.Icc 1 K, liouvilleR n * liouvilleAbelPhi t n =
          ∑ n ∈ Finset.Icc 1 K, liouvilleR n * (Real.exp (-(n * t)) / n) -
            ∑ n ∈ Finset.Icc 1 K, liouvilleR n * (1 / n) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [liouvilleAbelPhi]; ring
      have hshift : ∑ n ∈ Finset.Ico 1 K, sourcePartialSum liouvilleR n *
          (liouvilleAbelPhi t n - liouvilleAbelPhi t (n + 1 : ℕ)) =
          ∑ m ∈ Finset.range (K - 1), d t m := by
        rw [Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hd, hLf]; dsimp only
        rw [show 1 + m = m + 1 by ring]
      beta_reduce at habel
      rw [hshift] at habel
      rw [hsplit] at habel
      rw [hLf]
      linarith
    have h1 := tendsto_sum_Icc_liouvilleExpSum ht
    have h3 : Tendsto (fun K : ℕ => ∑ m ∈ Finset.range (K - 1), d t m) atTop (𝓝 (D t)) :=
      ((hds t ht).hasSum.tendsto_sum_nat).comp (Filter.tendsto_sub_atTop_nat 1)
    have h := h1.sub ((hbdry t ht).add h3)
    rw [zero_add] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with K hK
    exact (hid K hK).symm
  refine ⟨liouvilleExpSum 1 - D 1, CL * 2 ^ p * Z, by positivity, fun t ht => ?_⟩
  have heq : liouvilleExpSum t - D t = liouvilleExpSum 1 - D 1 :=
    tendsto_nhds_unique (hlim t ht) (hlim 1 one_pos)
  rw [show liouvilleExpSum t - (liouvilleExpSum 1 - D 1) = D t by linarith]
  exact hDb t ht

/-! ## The constant vanishes -/

theorem mellin_exp_neg {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) s = Gamma s := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [smul_eq_mul, mul_comm]

/-- **The constant vanishes.**  If `|J(t) − c₀| ≤ C t^q` for all `t > 0` with `0 < q ≤ 1`, then
`c₀ = 0`: `J − c₀e^{-t}` is `O(t^q)` at `0`, so its Mellin transform is continuous at `0`, while on
`Re s > 0` it equals the Liouville kernel minus `c₀Γ(s)` and `sΓ(s) → 1`. -/
theorem const_eq_zero_of_liouvilleExpSum_sub_const_le {c₀ C q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (h : ∀ t : ℝ, 0 < t → |liouvilleExpSum t - c₀| ≤ C * t ^ q) : c₀ = 0 := by
  set f : ℝ → ℂ := fun t => (liouvilleExpSum t : ℂ) - (c₀ : ℂ) * ((Real.exp (-t) : ℝ) : ℂ)
    with hf
  have hJc : ContinuousOn (fun t : ℝ => (liouvilleExpSum t : ℂ)) (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn continuousOn_liouvilleExpSum
  have hEc : Continuous fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ) := by fun_prop
  have hloc : LocallyIntegrableOn f (Ioi 0) :=
    (hJc.sub (continuousOn_const.mul hEc.continuousOn)).locallyIntegrableOn measurableSet_Ioi
  have hexpO : (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) =O[atTop] fun t => Real.exp (-1 * t) :=
    IsBigO.of_bound 1 (Eventually.of_forall fun t => by rw [Complex.norm_real, neg_one_mul, one_mul])
  have hbig : f =O[atTop] fun t => Real.exp (-1 * t) :=
    liouvilleExpSum_isBigO_atTop.sub (hexpO.const_mul_left (c₀ : ℂ))
  have hC : 0 ≤ C := by
    have := h 1 one_pos
    rw [Real.one_rpow, mul_one] at this
    exact le_trans (abs_nonneg _) this
  have hsmall : f =O[𝓝[>] 0] fun t : ℝ => t ^ (-(-q)) := by
    refine IsBigO.of_bound (C + |c₀|) ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    rw [neg_neg, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    have htq : t ≤ t ^ q := by
      calc t = t ^ (1 : ℝ) := (Real.rpow_one t).symm
        _ ≤ t ^ q := Real.rpow_le_rpow_of_exponent_ge ht0 ht1.le hq1
    have he : |1 - Real.exp (-t)| ≤ t := by
      have h1 := Real.add_one_le_exp (-t)
      have h2 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      rw [abs_of_nonneg (by linarith)]; linarith
    have hnorm : ‖f t‖ = |liouvilleExpSum t - c₀ * Real.exp (-t)| := by
      rw [hf]; dsimp only
      rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    calc |liouvilleExpSum t - c₀ * Real.exp (-t)| =
        |(liouvilleExpSum t - c₀) + c₀ * (1 - Real.exp (-t))| := by ring_nf
      _ ≤ |liouvilleExpSum t - c₀| + |c₀| * |1 - Real.exp (-t)| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ C * t ^ q + |c₀| * t ^ q :=
          add_le_add (h t ht0) (mul_le_mul_of_nonneg_left (he.trans htq) (abs_nonneg _))
      _ = (C + |c₀|) * t ^ q := by ring
  have hdiff : DifferentiableAt ℂ (mellin f) 0 :=
    mellin_differentiableAt_of_isBigO_rpow_exp one_pos hloc hbig hsmall (by simp; linarith)
  -- the Mellin identity on `Re s > 0`
  have hJbound : (fun t : ℝ => (liouvilleExpSum t : ℂ)) =O[𝓝[>] 0] fun t : ℝ => t ^ (-(0 : ℝ)) := by
    refine IsBigO.of_bound (C + |c₀|) ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    rw [neg_zero, Real.rpow_zero, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have := h t ht0
    have htq : t ^ q ≤ 1 := Real.rpow_le_one ht0.le ht1.le hq.le
    have : |liouvilleExpSum t| ≤ |liouvilleExpSum t - c₀| + |c₀| := by
      calc |liouvilleExpSum t| = |(liouvilleExpSum t - c₀) + c₀| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    nlinarith
  have hident : ∀ s : ℂ, 0 < s.re → mellin f s = liouvilleExpKernel s - (c₀ : ℂ) * Gamma s := by
    intro s hs
    have hJconv : MellinConvergent (fun t : ℝ => (liouvilleExpSum t : ℂ)) s :=
      mellinConvergent_of_isBigO_rpow_exp one_pos
        (hJc.locallyIntegrableOn measurableSet_Ioi) liouvilleExpSum_isBigO_atTop hJbound
        (by simpa using hs)
    have hEconv : MellinConvergent (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) s := by
      have := Complex.GammaIntegral_convergent hs
      refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp only [smul_eq_mul]; ring
    have hsub : mellin f s = mellin (fun t : ℝ => (liouvilleExpSum t : ℂ)) s -
        (c₀ : ℂ) * mellin (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) s := by
      rw [mellin, mellin, mellin, ← integral_const_mul, ← integral_sub hJconv
        (hEconv.const_mul (c₀ : ℂ))]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      simp only [hf, smul_eq_mul]; ring
    rw [hsub, mellin_liouvilleExpSum hs, Gamma_mul_LSeries_eq_kernel hs, mellin_exp_neg hs]
  -- continuity at `0`
  set g : ℂ → ℂ := fun s => s * mellin f s - s * liouvilleExpKernel s + (c₀ : ℂ) * Gamma (s + 1)
    with hg
  have hkernel : ContinuousAt liouvilleExpKernel 0 := by
    unfold liouvilleExpKernel
    have hG1 : ContinuousAt Gamma ((0 : ℂ) + 1) :=
      (analyticAt_Gamma_of_pos_re (by simp)).continuousAt
    have hG : ContinuousAt (fun z : ℂ => Gamma (z + 1)) 0 :=
      ContinuousAt.comp (g := Gamma) (f := fun z : ℂ => z + 1) hG1
        (continuousAt_id.add continuousAt_const)
    have hZ1 : ContinuousAt (fun z : ℂ => zetaResidueUnit (2 * z + 2)) 0 :=
      (analyticAt_zetaResidueUnit _).continuousAt.comp
        ((continuousAt_const.mul continuousAt_id).add continuousAt_const)
    have hZ2 : ContinuousAt (fun z : ℂ => zetaResidueUnit (z + 1)) 0 :=
      (analyticAt_zetaResidueUnit _).continuousAt.comp (continuousAt_id.add continuousAt_const)
    refine (hG.mul hZ1).div (((continuousAt_const.mul continuousAt_id).add continuousAt_const).mul
      hZ2) ?_
    simp
  have hgc : ContinuousAt g 0 := by
    have hG1 : ContinuousAt Gamma ((0 : ℂ) + 1) :=
      (analyticAt_Gamma_of_pos_re (by simp)).continuousAt
    have hG : ContinuousAt (fun z : ℂ => Gamma (z + 1)) 0 :=
      ContinuousAt.comp (g := Gamma) (f := fun z : ℂ => z + 1) hG1
        (continuousAt_id.add continuousAt_const)
    exact ((continuousAt_id.mul hdiff.continuousAt).sub (continuousAt_id.mul hkernel)).add
      (continuousAt_const.mul hG)
  have hg0 : g 0 = (c₀ : ℂ) := by simp [hg]
  have hgpos : ∀ x : ℝ, 0 < x → g x = 0 := by
    intro x hx
    have hs : 0 < (x : ℂ).re := by simpa using hx
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    rw [hg]; dsimp only
    rw [hident x hs, Complex.Gamma_add_one _ hx0]
    ring
  have ht : Tendsto (fun x : ℝ => g x) (𝓝[>] 0) (𝓝 (g 0)) := by
    have := (ContinuousAt.comp_of_eq hgc Complex.continuous_ofReal.continuousAt
      (by simp : ((0 : ℝ) : ℂ) = 0)).tendsto
    exact this.mono_left nhdsWithin_le_nhds
  have ht' : Tendsto (fun x : ℝ => g x) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hgpos x hx).symm
  have := tendsto_nhds_unique ht ht'
  rw [hg0] at this
  exact_mod_cast this

/-- **A summatory power bound gives the power bound for `J`.** -/
theorem liouvilleExpSum_isBigO_of_summatory
    (hL : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |sourcePartialSum liouvilleR N| ≤ C * ((N : ℝ) + 1) ^ (1 / 2 + δ)) {ε : ℝ}
    (hε : 0 < ε) :
    (fun t : ℝ => liouvilleExpSum t) =O[𝓝[>] 0] fun t => t ^ (1 / 2 - ε) := by
  set δ := min (ε / 2) (1 / 8) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ4 : δ < 1 / 4 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨c₀, C, hC, hdec⟩ := exists_liouvilleExpSum_sub_const_le hδ0 hδ4 (hL δ hδ0)
  have hc₀ := const_eq_zero_of_liouvilleExpSum_sub_const_le (q := 1 / 2 - 2 * δ)
    (by linarith) (by linarith) hdec
  rw [hc₀] at hdec
  refine IsBigO.of_bound C ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  obtain ⟨ht0, ht1⟩ := ht
  have := hdec t ht0
  rw [sub_zero] at this
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
  refine le_trans this (mul_le_mul_of_nonneg_left ?_ hC)
  exact Real.rpow_le_rpow_of_exponent_ge ht0 ht1.le (by
    have := min_le_left (ε / 2) (1 / 8); linarith)

/-- **RH gives the power bound for `J`.** -/
theorem liouvilleExpSum_isBigO_of_riemannHypothesis (hRH : RiemannHypothesis) {ε : ℝ}
    (hε : 0 < ε) :
    (fun t : ℝ => liouvilleExpSum t) =O[𝓝[>] 0] fun t => t ^ (1 / 2 - ε) :=
  liouvilleExpSum_isBigO_of_summatory
    (fun _ hδ => exists_abs_sourcePartialSum_liouvilleR_le_of_riemannHypothesis hRH hδ) hε

/-- **The Liouville summatory law is equivalent to RH.**
`RH ⟺ ∀ δ > 0, Σ_{n ≤ N} λ(n) = O(N^{½+δ})`. -/
theorem riemannHypothesis_iff_forall_liouvilleSummatory_le :
    RiemannHypothesis ↔ ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |sourcePartialSum liouvilleR N| ≤ C * ((N : ℝ) + 1) ^ (1 / 2 + δ) :=
  ⟨fun hRH _ hδ => exists_abs_sourcePartialSum_liouvilleR_le_of_riemannHypothesis hRH hδ,
    fun hL => riemannHypothesis_of_forall_liouvilleExpSum_isBigO fun _ hε =>
      liouvilleExpSum_isBigO_of_summatory hL hε⟩

/-- **The Liouville power law is equivalent to RH.**
`RH ⟺ ∀ ε > 0, Σ λ(n) e^{-nt}/n = O(t^{½-ε})` as `t → 0⁺`. -/
theorem riemannHypothesis_iff_forall_liouvilleExpSum_isBigO :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => liouvilleExpSum t) =O[𝓝[>] 0] fun t => t ^ (1 / 2 - ε) :=
  ⟨fun hRH _ hε => liouvilleExpSum_isBigO_of_riemannHypothesis hRH hε,
    riemannHypothesis_of_forall_liouvilleExpSum_isBigO⟩

end

end RHTower
