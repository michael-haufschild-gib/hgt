import GaloisForLFunctions.ArithmeticEffectivityTheory.TheBurgessBound
import GaloisForLFunctions.RHTower.MertensSecondRealVariable

/-!
# The least quadratic non-residue is at most `p^{1/(4√e) + ε}`

Burgess's bound combined with Vinogradov's trick. If every `n ≤ y` is a quadratic residue
modulo `p`, then `χ(n) = 1` for every `n` whose prime factors are `≤ y` (`chiR_eq_one_of_smooth`),
so for `x ≥ y`

  `Σ_{n ≤ x} χ(n) ≥ x − 2x Σ_{y < q ≤ x} 1/q`  (`sum_chiR_ge_vinogradov`).

With `x = y^u`, Mertens gives `Σ_{y<q≤x} 1/q → log u`, which is `< 1/2` for `u < √e`; Burgess makes
the left side `o(x)` once `x = p^{1/4+δ}`. Hence (`eventually_exists_nonresidue_le`) for every
`ε > 0` and every large prime `p` there is a non-residue `n ≤ p^{1/(4√e)+ε}`.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticEffectivityTheory

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Smooth numbers are residues**: if every `1 ≤ n ≤ y` has `χ(n) = 1`, then so does every
nonzero `n` all of whose prime factors are `≤ y`. -/
theorem chiR_eq_one_of_smooth {y : ℕ} (hres : ∀ q : ℕ, q.Prime → q ≤ y → chiR (q : ZMod p) = 1) :
    ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → q ∣ n → q ≤ y) → chiR (n : ZMod p) = 1 := by
  intro n
  induction n using induction_on_primes with
  | zero => intro h; exact absurd rfl h
  | one => intro _ _; rw [Nat.cast_one, chiR_one]
  | prime_mul q a hq ih =>
    intro hqa hsm
    have ha : a ≠ 0 := fun h => hqa (by rw [h, mul_zero])
    rw [Nat.cast_mul, chiR_mul, hres q hq (hsm q hq (dvd_mul_right q a)),
      ih ha fun q' hq' hdvd => hsm q' hq' (dvd_mul_of_dvd_right hdvd q), one_mul]

omit hp in
/-- `Σ_{y < q ≤ x} 1/q = Σ_{p ≤ x} 1/p − Σ_{p ≤ y} 1/p`. -/
theorem primeRecipSum_sub_eq {x y : ℕ} (hyx : y ≤ x) :
    RHTower.primeRecipSum x - RHTower.primeRecipSum y =
      ∑ q ∈ (Ioc y x).filter Nat.Prime, (1 / (q : ℝ)) := by
  have hrange : ∀ N : ℕ, Icc 0 N = range (N + 1) := by
    intro N; ext n; simp [Finset.mem_Icc, Finset.mem_range]
  unfold RHTower.primeRecipSum
  rw [hrange, hrange, ← Finset.sum_range_add_sum_Ico _ (by omega : y + 1 ≤ x + 1),
    add_sub_cancel_left, Finset.sum_filter]
  have hIco : Ico (y + 1) (x + 1) = Ioc y x := by
    ext n; simp [Finset.mem_Ico, Finset.mem_Ioc]
  rw [hIco]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [RHTower.primeRecipWeight]

omit hp in
/-- **Few numbers have a large prime factor**: `#{n ≤ x : ∃ q > y prime, q ∣ n} ≤ x Σ_{y<q≤x} 1/q`. -/
theorem card_bad_le {x y : ℕ} (hyx : y ≤ x) :
    (((Icc 1 x).filter fun n => ∃ q ∈ Ioc y n, q.Prime ∧ q ∣ n).card : ℝ) ≤
      x * (RHTower.primeRecipSum x - RHTower.primeRecipSum y) := by
  set Q := (Ioc y x).filter Nat.Prime
  have hsub : (Icc 1 x).filter (fun n => ∃ q ∈ Ioc y n, q.Prime ∧ q ∣ n) ⊆
      Q.biUnion fun q => (Icc 1 x).filter fun n => q ∣ n := by
    intro n hn
    obtain ⟨hn, q, hqI, hq, hqn⟩ := Finset.mem_filter.mp hn
    have hn1 := Finset.mem_Icc.mp hn
    obtain ⟨hyq, hqle⟩ := Finset.mem_Ioc.mp hqI
    refine Finset.mem_biUnion.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hyq, by omega⟩, hq⟩,
      Finset.mem_filter.mpr ⟨hn, hqn⟩⟩
  have hcount : ∀ q ∈ Q, ((((Icc 1 x).filter fun n => q ∣ n).card : ℕ) : ℝ) ≤ x * (1 / (q : ℝ)) := by
    intro q hq
    have hq0 : (0 : ℝ) < q := by
      have := (Finset.mem_filter.mp hq).2.pos; exact_mod_cast this
    have : (Icc 1 x).filter (fun n => q ∣ n) = (Ioc 0 x).filter (fun n => q ∣ n) := rfl
    rw [this, Nat.Ioc_filter_dvd_card_eq_div, mul_one_div, le_div_iff₀ hq0]
    exact_mod_cast Nat.div_mul_le_self x q
  calc (((Icc 1 x).filter fun n => ∃ q ∈ Ioc y n, q.Prime ∧ q ∣ n).card : ℝ)
      ≤ ((Q.biUnion fun q => (Icc 1 x).filter fun n => q ∣ n).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ q ∈ Q, ((((Icc 1 x).filter fun n => q ∣ n).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ q ∈ Q, x * (1 / (q : ℝ)) := Finset.sum_le_sum hcount
    _ = _ := by rw [← Finset.mul_sum, primeRecipSum_sub_eq hyx]

/-- **Vinogradov's lower bound**: if every `1 ≤ n ≤ y < p` is a residue, then for `x ≥ y`,
`Σ_{1 ≤ n ≤ x} χ(n) ≥ x − 2x Σ_{y<q≤x} 1/q`. -/
theorem sum_chiR_ge_vinogradov {x y : ℕ} (hyp : y < p)
    (hsq : ∀ n : ℕ, 1 ≤ n → n ≤ y → IsSquare (n : ZMod p)) (hyx : y ≤ x) :
    (x : ℝ) - 2 * (x * (RHTower.primeRecipSum x - RHTower.primeRecipSum y)) ≤
      ∑ n ∈ Icc 1 x, chiR (n : ZMod p) := by
  have hres : ∀ q : ℕ, q.Prime → q ≤ y → chiR (q : ZMod p) = 1 := by
    intro q hq hqy
    exact chiR_eq_one (natCast_ne_zero_of_lt hq.pos (by omega)) (hsq q hq.one_lt.le hqy)
  set bad : ℕ → Prop := fun n => ∃ q ∈ Ioc y n, q.Prime ∧ q ∣ n with hbad
  have hgood : ∀ n ∈ (Icc 1 x).filter (fun n => ¬ bad n), chiR (n : ZMod p) = 1 := by
    intro n hn
    obtain ⟨hn, hnb⟩ := Finset.mem_filter.mp hn
    refine chiR_eq_one_of_smooth hres n (by have := (Finset.mem_Icc.mp hn).1; omega) ?_
    intro q hq hqn
    by_contra h
    have hn1 := (Finset.mem_Icc.mp hn).1
    exact hnb ⟨q, Finset.mem_Ioc.mpr ⟨by omega, Nat.le_of_dvd (by omega) hqn⟩, hq, hqn⟩
  have hb := card_bad_le (x := x) (y := y) hyx
  rw [← Finset.sum_filter_add_sum_filter_not (Icc 1 x) bad]
  have hsum_good : ∑ n ∈ (Icc 1 x).filter (fun n => ¬ bad n), chiR (n : ZMod p) =
      ((Icc 1 x).filter (fun n => ¬ bad n)).card := by
    rw [Finset.sum_congr rfl hgood, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsum_bad : -(((Icc 1 x).filter bad).card : ℝ) ≤
      ∑ n ∈ (Icc 1 x).filter bad, chiR (n : ZMod p) := by
    have : ∑ n ∈ (Icc 1 x).filter bad, (-1 : ℝ) ≤ ∑ n ∈ (Icc 1 x).filter bad, chiR (n : ZMod p) :=
      Finset.sum_le_sum fun n _ => (abs_le.mp (abs_chiR_le _)).1
    simpa using this
  have hcard : (((Icc 1 x).filter (fun n => ¬ bad n)).card : ℝ) =
      x - ((Icc 1 x).filter bad).card := by
    have := Finset.card_filter_add_card_filter_not (s := Icc 1 x) bad
    rw [Nat.card_Icc] at this
    have h' : (((Icc 1 x).filter bad).card : ℝ) + ((Icc 1 x).filter (fun n => ¬ bad n)).card = x := by
      exact_mod_cast (by omega : ((Icc 1 x).filter bad).card +
        ((Icc 1 x).filter (fun n => ¬ bad n)).card = x)
    linarith
  rw [hsum_good, hcard]
  linarith

/-- `S(1, x) = Σ_{1 ≤ n ≤ x} χ(n)`. -/
theorem burgessS_one_eq (x : ℕ) : burgessS p 1 x = ∑ n ∈ Icc 1 x, chiR (n : ZMod p) := by
  unfold burgessS
  refine Finset.sum_nbij' (fun k => k + 1) (fun n => n - 1) ?_ ?_ ?_ ?_ ?_
  · intro k hk; rw [Finset.mem_range] at hk; rw [Finset.mem_Icc]; omega
  · intro n hn; rw [Finset.mem_Icc] at hn; rw [Finset.mem_range]; omega
  · intro k _; simp
  · intro n hn; rw [Finset.mem_Icc] at hn; show n - 1 + 1 = n; omega
  · intro k _; push_cast; ring_nf

omit hp in
/-- **Mertens on a window**: `Σ_{X < q ≤ X^u} 1/q → log u`. -/
theorem tendsto_primeRecipSum_window {u : ℝ} (hu : 0 < u) :
    Tendsto (fun X : ℝ => RHTower.primeRecipSum ⌊X ^ u⌋₊ - RHTower.primeRecipSum ⌊X⌋₊) atTop
      (𝓝 (Real.log u)) := by
  have hM := RHTower.tendsto_primeRecipSum_floor_sub_logLog
  have hMu := hM.comp (tendsto_rpow_atTop hu)
  have hdiff := hMu.sub hM
  rw [sub_self] at hdiff
  have hcongr : (fun X : ℝ => RHTower.primeRecipSum ⌊X ^ u⌋₊ - RHTower.primeRecipSum ⌊X⌋₊) =ᶠ[atTop]
      fun X => ((fun t : ℝ => RHTower.primeRecipSum ⌊t⌋₊ - Real.log (Real.log t)) ∘
        (fun X : ℝ => X ^ u)) X -
        (RHTower.primeRecipSum ⌊X⌋₊ - Real.log (Real.log X)) + Real.log u := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hlogX : 0 < Real.log X := Real.log_pos hX
    simp only [Function.comp]
    rw [Real.log_rpow (by linarith), Real.log_mul hu.ne' hlogX.ne']
    ring
  refine (Tendsto.congr' hcongr.symm ?_)
  simpa using hdiff.add_const (Real.log u)

omit hp in
theorem tendsto_rpow_neg_mul_log {η : ℝ} (hη : 0 < η) :
    Tendsto (fun t : ℝ => t ^ (-η) * (1 + Real.log t)) atTop (𝓝 0) := by
  have h1 := tendsto_rpow_neg_atTop hη
  have h2 : Tendsto (fun t : ℝ => Real.log t / t ^ η) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hη).tendsto_div_nhds_zero
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [Real.rpow_neg ht.le, mul_add, mul_one, div_eq_inv_mul]

omit hp in
theorem sqrt_exp_bounds : 1.6 < Real.sqrt (Real.exp 1) ∧ Real.sqrt (Real.exp 1) < 2 := by
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num; linarith
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num; linarith

omit hp in
theorem log_sqrt_exp : Real.log (Real.sqrt (Real.exp 1)) = 1 / 2 := by
  rw [Real.log_sqrt (Real.exp_pos 1).le, Real.log_exp]

omit hp in
/-- The case `ε ≤ 1/10`. -/
theorem eventually_exists_nonresidue_le_aux {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10) :
    ∀ᶠ p : ℕ in atTop, p.Prime → ∃ n : ℕ, 1 ≤ n ∧
      (n : ℝ) ≤ (p : ℝ) ^ (1 / (4 * Real.sqrt (Real.exp 1)) + ε) ∧ ¬ IsSquare (n : ZMod p) := by
  set e := Real.sqrt (Real.exp 1)
  obtain ⟨he1, he2⟩ := sqrt_exp_bounds
  have he0 : 0 < e := by linarith
  set β := 1 / (4 * e) + ε
  set u := e / (1 + 2 * e * ε)
  set α := u * β
  have hβ0 : 0 < β := by positivity
  have hden : 0 < 1 + 2 * e * ε := by positivity
  have hu1 : 1 < u := by
    rw [lt_div_iff₀ hden]; nlinarith
  have hu0 : 0 < u := by linarith
  have hus : u < e := by
    rw [div_lt_iff₀ hden]; nlinarith [mul_pos (mul_pos he0 he0) hε]
  have hlogu : Real.log u < 1 / 2 := by
    rw [← log_sqrt_exp]; exact Real.log_lt_log hu0 hus
  set c := 1 / 2 - Real.log u
  have hc : 0 < c := by simp only [c]; linarith
  have hαeq : α = (1 + 4 * e * ε) / (4 * (1 + 2 * e * ε)) := by
    simp only [α, u, β]; field_simp
  set δ := α - 1 / 4
  have hδ : 0 < δ := by
    simp only [δ]; rw [hαeq, sub_pos, lt_div_iff₀ (by positivity)]; nlinarith
  have hβα : β ≤ α := by
    simp only [α]; nlinarith
  have hβ1 : β < 1 := by
    simp only [β]
    have : 1 / (4 * e) < 1 / 2 := by rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  -- the Burgess exponent
  set r := ⌈1 / δ⌉₊ + 2
  have hr : 2 ≤ r := by omega
  have hr0 : (0 : ℝ) < r := by positivity
  have hrδ : 1 / (r : ℝ) ≤ δ := by
    have h1 : 1 / δ ≤ r := by
      have := Nat.le_ceil (1 / δ)
      have : (⌈1 / δ⌉₊ : ℝ) ≤ r := by simp only [r]; push_cast; linarith
      linarith
    rw [div_le_iff₀ hr0]
    rw [div_le_iff₀ hδ] at h1
    linarith
  set ex := ((r : ℝ) + 1) / (4 * (r : ℝ) ^ 2)
  set η := α / r - ex
  have hη : 0 < η := by
    have hex : ex = 1 / (4 * r) + 1 / (4 * r) * (1 / r) := by
      simp only [ex]; field_simp
    simp only [η]
    rw [hex]
    have h1 : 1 / (4 * (r : ℝ)) * (1 / r) ≤ 1 / (4 * r) * δ :=
      mul_le_mul_of_nonneg_left hrδ (by positivity)
    have h2 : α / r = (1 / 4 + δ) / r := by simp only [δ]; ring
    rw [h2]
    have h3 : (1 / 4 + δ) / (r : ℝ) - (1 / (4 * r) + 1 / (4 * r) * δ) = δ * (3 / 4) / r := by
      field_simp; ring
    nlinarith [div_pos (mul_pos hδ (by norm_num : (0 : ℝ) < 3 / 4)) hr0]
  set K := burgessConst r
  -- eventually: the Mertens window is below `log u + c/2`
  have hX : Tendsto (fun p : ℕ => (p : ℝ) ^ β) atTop atTop :=
    (tendsto_rpow_atTop hβ0).comp tendsto_natCast_atTop_atTop
  have hW := (tendsto_primeRecipSum_window hu0).comp hX
  have hW' : ∀ᶠ p : ℕ in atTop, RHTower.primeRecipSum ⌊((p : ℝ) ^ β) ^ u⌋₊ -
      RHTower.primeRecipSum ⌊(p : ℝ) ^ β⌋₊ < Real.log u + c / 2 :=
    hW.eventually (gt_mem_nhds (by linarith))
  -- eventually: the Burgess saving beats the logarithm
  have hD := (tendsto_rpow_neg_mul_log hη).comp tendsto_natCast_atTop_atTop
  have hD' : ∀ᶠ p : ℕ in atTop, K * (((p : ℝ)) ^ (-η) * (1 + Real.log p)) < c / 2 := by
    have := (hD.const_mul K).eventually (gt_mem_nhds (show K * 0 < c / 2 by rw [mul_zero]; linarith))
    simpa using this
  filter_upwards [hW', hD', eventually_ge_atTop 3] with p hWp hDp hp2 hprime
  haveI : Fact p.Prime := ⟨hprime⟩
  by_contra hno
  push Not at hno
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hp0 : (0 : ℝ) < p := by linarith
  set y := ⌊(p : ℝ) ^ β⌋₊
  set x := ⌊(p : ℝ) ^ α⌋₊
  have hpα : ((p : ℝ) ^ β) ^ u = (p : ℝ) ^ α := by
    rw [← Real.rpow_mul hp0.le]; simp only [α]; ring_nf
  rw [hpα] at hWp
  have hyβ : (y : ℝ) ≤ (p : ℝ) ^ β := Nat.floor_le (by positivity)
  have hyp : y < p := by
    have : (p : ℝ) ^ β < p := by
      calc (p : ℝ) ^ β < (p : ℝ) ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hp1 hβ1
        _ = p := Real.rpow_one _
    have : (y : ℝ) < p := lt_of_le_of_lt hyβ this
    exact_mod_cast this
  have hyx : y ≤ x := Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hp1.le hβα)
  have hsq : ∀ n : ℕ, 1 ≤ n → n ≤ y → IsSquare (n : ZMod p) := by
    intro n hn1 hny
    by_contra h
    have : (n : ℝ) ≤ (p : ℝ) ^ β := le_trans (by exact_mod_cast hny) hyβ
    exact h (hno n hn1 this)
  have hV := sum_chiR_ge_vinogradov hyp hsq hyx
  have hB := abs_burgessS_le (p := p) (by omega) hr x 1
  rw [burgessS_one_eq] at hB
  -- `x ≥ p^α/2` and `x ≤ p^α`
  have hpα1 : (1 : ℝ) ≤ (p : ℝ) ^ α := Real.one_le_rpow hp1.le (by linarith)
  have hxα : (x : ℝ) ≤ (p : ℝ) ^ α := Nat.floor_le (by positivity)
  have hxα' : (p : ℝ) ^ α / 2 ≤ x := by
    have := Nat.lt_floor_add_one ((p : ℝ) ^ α)
    have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast Nat.le_floor (by exact_mod_cast hpα1)
    linarith
  set L := 1 + Real.log p
  have hL : 0 < L := by have := Real.log_nonneg hp1.le; simp only [L]; linarith
  set P := (p : ℝ) ^ ex
  -- Vinogradov's lower bound against Burgess's upper bound
  have hlow : c * x ≤ ∑ n ∈ Icc 1 x, chiR (n : ZMod p) := by
    have : (x : ℝ) * c ≤ x - 2 * (x * (RHTower.primeRecipSum x - RHTower.primeRecipSum y)) := by
      have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg _
      have hw : 0 ≤ 1 - 2 * (RHTower.primeRecipSum x - RHTower.primeRecipSum y) - c := by
        simp only [c] at hWp ⊢; linarith
      have := mul_nonneg hx0 hw
      linarith
    linarith
  have hup : ∑ n ∈ Icc 1 x, chiR (n : ZMod p) ≤ K * (x : ℝ) ^ (1 - 1 / (r : ℝ)) * P * L :=
    (le_abs_self _).trans hB
  have hxθ : (x : ℝ) ^ (1 - 1 / (r : ℝ)) ≤ ((p : ℝ) ^ α) ^ (1 - 1 / (r : ℝ)) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hxα (by
      have : 1 / (r : ℝ) ≤ 1 := by rw [div_le_one hr0]; exact_mod_cast (by omega : 1 ≤ r)
      linarith)
  have hK : 0 ≤ K := by
    simp only [K, burgessConst]
    have := one_le_burgessMainConst (by omega : 1 ≤ r); linarith
  have hexp : ((p : ℝ) ^ α) ^ (1 - 1 / (r : ℝ)) * P = (p : ℝ) ^ α * (p : ℝ) ^ (-η) := by
    simp only [P]
    rw [← Real.rpow_mul hp0.le, ← Real.rpow_add hp0, ← Real.rpow_add hp0]
    congr 1
    simp only [η]; ring
  have hchain : c * ((p : ℝ) ^ α / 2) ≤ K * ((p : ℝ) ^ α * (p : ℝ) ^ (-η)) * L := by
    calc c * ((p : ℝ) ^ α / 2) ≤ c * x := mul_le_mul_of_nonneg_left hxα' hc.le
      _ ≤ K * (x : ℝ) ^ (1 - 1 / (r : ℝ)) * P * L := hlow.trans hup
      _ = K * ((x : ℝ) ^ (1 - 1 / (r : ℝ)) * P) * L := by ring
      _ ≤ K * (((p : ℝ) ^ α) ^ (1 - 1 / (r : ℝ)) * P) * L :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hxθ (Real.rpow_nonneg hp0.le _)) hK) hL.le
      _ = K * ((p : ℝ) ^ α * (p : ℝ) ^ (-η)) * L := by rw [hexp]
  have hpαpos : 0 < (p : ℝ) ^ α := by positivity
  have : c / 2 ≤ K * ((p : ℝ) ^ (-η) * L) := by
    have h' : (p : ℝ) ^ α * (c / 2) ≤ (p : ℝ) ^ α * (K * ((p : ℝ) ^ (-η) * L)) := by
      have e1 : c * ((p : ℝ) ^ α / 2) = (p : ℝ) ^ α * (c / 2) := by ring
      have e2 : K * ((p : ℝ) ^ α * (p : ℝ) ^ (-η)) * L = (p : ℝ) ^ α * (K * ((p : ℝ) ^ (-η) * L)) := by
        ring
      rw [← e1, ← e2]; exact hchain
    exact le_of_mul_le_mul_left h' hpαpos
  simp only [L] at this
  linarith

/-- **The least quadratic non-residue** (Burgess–Vinogradov). For every `ε > 0` and every
sufficiently large prime `p` there is a quadratic non-residue `1 ≤ n ≤ p^{1/(4√e) + ε}`. -/
theorem eventually_exists_nonresidue_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop, p.Prime → ∃ n : ℕ, 1 ≤ n ∧
      (n : ℝ) ≤ (p : ℝ) ^ (1 / (4 * Real.sqrt (Real.exp 1)) + ε) ∧ ¬ IsSquare (n : ZMod p) := by
  set ε₀ := min ε (1 / 10)
  have h₀ := eventually_exists_nonresidue_le_aux (ε := ε₀) (lt_min hε (by norm_num))
    (min_le_right _ _)
  filter_upwards [h₀, eventually_ge_atTop 1] with p hp hp1 hprime
  obtain ⟨n, hn1, hn, hsq⟩ := hp hprime
  refine ⟨n, hn1, hn.trans ?_, hsq⟩
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp1) (by
    have := min_le_left ε (1 / 10); linarith)

end GaloisForLFunctions.ArithmeticEffectivityTheory
