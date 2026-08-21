import GaloisForLFunctions.HTGeometry.KleinbockMargulis.Setup

/-!
# Reduction to a statement about lattices (Kleinbock–Margulis, §2)

Lemma 2.1 turns one solution of the multiplicative approximation inequality (1.1M) into a short
vector of the lattice `g_t Λ_y`: if `|q · y + p| Π₊(q) ≤ Π₊(q)^{-ε}` and one sets
`r = Π₊(q)^{-ε/(n+1)}` and `max(|qᵢ|, 1) = r e^{tᵢ}`, then `δ(g_t Λ_y) ≤ r`.

An elementary computation identifies `r` with `e^{-γ t}` for `γ = ε/(n + 1 + nε)`, and rounding
`t` down to integers costs at most a factor `e`; Corollary 2.2 therefore produces infinitely many
`t ∈ ℤ₊ⁿ` with `δ(g_t Λ_y) ≤ e^{-γ t}` whenever `y` is very well multiplicatively approximable.

## Main results

* `lemma_2_1` — Lemma 2.1.
* `corollary_2_2` — Corollary 2.2.
-/

open Matrix Finset Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

variable {n : ℕ}

/-! ### Lemma 2.1 -/

/-- **Lemma 2.1.**  A solution of (1.1M) gives a lattice vector of `g_t Λ_y` of norm at most `r`. -/
theorem lemma_2_1 {ε r : ℝ} {t : Fin n → ℝ} (hr : 0 < r) (y : Fin n → ℝ) (p : ℤ)
    {q : Fin n → ℤ} (hq0 : q ≠ 0)
    (hq : |dotProd q y + (p : ℝ)| * PiPlus q ≤ PiPlus q ^ (-ε))
    (hrdef : r ^ (n + 1) = PiPlus q ^ (-ε))
    (ht : ∀ i, max |(q i : ℝ)| 1 = r * Real.exp (t i)) :
    latticeDelta (flowMat t * unipotentMat y) ≤ r := by
  classical
  set v : Fin (n + 1) → ℤ := Fin.cons p q with hv
  have hvne : v ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i, q i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hq0 (funext hcon)
    intro hcon
    have := congrFun hcon i.succ
    rw [hv] at this
    simp only [Fin.cons_succ, Pi.zero_apply] at this
    exact hi this
  have hcast : (fun i => ((v i : ℤ) : ℝ)) = Fin.cons (p : ℝ) fun i => (q i : ℝ) := by
    funext i
    refine Fin.cases ?_ (fun i' => ?_) i <;> simp [hv]
  -- (2.4): `Π₊(q) = r^n e^{t}`
  have hprod : PiPlus q = r ^ n * Real.exp (∑ i, t i) := by
    rw [PiPlus, Real.exp_sum]
    rw [Finset.prod_congr rfl fun i _ => ht i, Finset.prod_mul_distrib]
    simp
  have hexp : Real.exp (∑ i, t i) = PiPlus q / r ^ n := by
    rw [hprod]; field_simp
  -- the norm estimate
  have hnorm : ‖(flowMat t * unipotentMat y).mulVec fun i => ((v i : ℤ) : ℝ)‖ ≤ r := by
    rw [hcast, ← Matrix.mulVec_mulVec, unipotentMat_mulVec, flowMat_mulVec]
    refine (pi_norm_le_iff_of_nonneg hr.le).mpr fun i => ?_
    refine Fin.cases ?_ (fun i' => ?_) i
    · -- (2.3a)
      simp only [Fin.cons_zero, latticeVec, Real.norm_eq_abs, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      have hP : (0:ℝ) < PiPlus q := PiPlus_pos q
      have h1 : |dotProd q y + (p : ℝ)| ≤ PiPlus q ^ (-ε) / PiPlus q :=
        (le_div_iff₀ hP).mpr hq
      calc Real.exp (∑ i, t i) * |dotProd q y + (p : ℝ)|
          ≤ (PiPlus q / r ^ n) * (PiPlus q ^ (-ε) / PiPlus q) := by
            rw [hexp]
            exact mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = PiPlus q ^ (-ε) / r ^ n := by field_simp
        _ = r ^ (n + 1) / r ^ n := by rw [hrdef]
        _ = r := by rw [pow_succ]; field_simp
    · -- (2.3b)
      simp only [Fin.cons_succ, latticeVec, Real.norm_eq_abs, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      have h1 : |(q i' : ℝ)| ≤ r * Real.exp (t i') := by
        rw [← ht i']; exact le_max_left _ _
      calc Real.exp (-(t i')) * |(q i' : ℝ)| ≤ Real.exp (-(t i')) * (r * Real.exp (t i')) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = r := by
            rw [show Real.exp (-(t i')) * (r * Real.exp (t i'))
              = r * (Real.exp (-(t i')) * Real.exp (t i')) by ring, ← Real.exp_add]
            simp
  exact le_trans (latticeDelta_le _ hvne) hnorm

/-! ### Corollary 2.2 -/

/-- The radius `r = Π₊(q)^{-ε/(n+1)}` attached to a solution of (1.1M). -/
noncomputable def radiusOf (ε : ℝ) (n : ℕ) (q : Fin n → ℤ) : ℝ :=
  Real.exp (-(ε / (n + 1)) * Real.log (PiPlus q))

/-- The exponents `tᵢ = log(max(|qᵢ|,1)/r)`. -/
noncomputable def expOf (ε : ℝ) (n : ℕ) (q : Fin n → ℤ) : Fin n → ℝ :=
  fun i => Real.log (max |(q i : ℝ)| 1 / radiusOf ε n q)

theorem radiusOf_pos (ε : ℝ) (n : ℕ) (q : Fin n → ℤ) : 0 < radiusOf ε n q := Real.exp_pos _

theorem radiusOf_le_one {ε : ℝ} (hε : 0 < ε) (n : ℕ) (q : Fin n → ℤ) : radiusOf ε n q ≤ 1 := by
  rw [radiusOf, Real.exp_le_one_iff]
  have h1 : 0 ≤ Real.log (PiPlus q) := Real.log_nonneg (one_le_PiPlus q)
  have h2 : 0 < ε / (n + 1) := by positivity
  nlinarith

theorem max_eq_radiusOf_mul_exp (ε : ℝ) (n : ℕ) (q : Fin n → ℤ) (i : Fin n) :
    max |(q i : ℝ)| 1 = radiusOf ε n q * Real.exp (expOf ε n q i) := by
  have hpos : (0:ℝ) < max |(q i : ℝ)| 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hr : (0:ℝ) < radiusOf ε n q := radiusOf_pos ε n q
  rw [expOf, Real.exp_log (div_pos hpos hr)]
  field_simp

theorem expOf_nonneg {ε : ℝ} (hε : 0 < ε) (n : ℕ) (q : Fin n → ℤ) (i : Fin n) :
    0 ≤ expOf ε n q i := by
  rw [expOf]
  refine Real.log_nonneg ?_
  rw [le_div_iff₀ (radiusOf_pos ε n q)]
  have h1 : radiusOf ε n q ≤ 1 := radiusOf_le_one hε n q
  have h2 : (1:ℝ) ≤ max |(q i : ℝ)| 1 := le_max_right _ _
  nlinarith

/-- The relation `r^{n+1} = Π₊(q)^{-ε}`. -/
theorem radiusOf_pow {ε : ℝ} (n : ℕ) (q : Fin n → ℤ) :
    radiusOf ε n q ^ (n + 1) = PiPlus q ^ (-ε) := by
  rw [radiusOf, ← Real.exp_nat_mul, Real.rpow_def_of_pos (PiPlus_pos q)]
  congr 1
  push_cast
  field_simp

/-- The exponent identity `r = e^{-γ t}` with `γ = ε/(n+1+nε)`. -/
theorem radiusOf_eq_exp_neg_gamma {ε : ℝ} (hε : 0 < ε) (n : ℕ) (q : Fin n → ℤ) :
    radiusOf ε n q
      = Real.exp (-(ε / ((n : ℝ) + 1 + n * ε) * ∑ i, expOf ε n q i)) := by
  set L := Real.log (PiPlus q) with hL
  have hsum : (∑ i, expOf ε n q i) = ((n : ℝ) + 1 + n * ε) / ((n : ℝ) + 1) * L := by
    have hprod : PiPlus q = radiusOf ε n q ^ n * Real.exp (∑ i, expOf ε n q i) := by
      rw [PiPlus, Real.exp_sum,
        Finset.prod_congr rfl fun i _ => max_eq_radiusOf_mul_exp ε n q i,
        Finset.prod_mul_distrib]
      simp
    have h1 : Real.exp L = PiPlus q := Real.exp_log (PiPlus_pos q)
    have h2 : radiusOf ε n q ^ n = Real.exp (-(ε / ((n:ℝ) + 1)) * L * n) := by
      rw [radiusOf, ← Real.exp_nat_mul, hL]
      ring_nf
    rw [h2, ← Real.exp_add] at hprod
    rw [← h1] at hprod
    have := Real.exp_injective hprod
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp at this ⊢
    linarith [this]
  rw [hsum, radiusOf]
  congr 1
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hn2 : ((n : ℝ) + 1 + n * ε) ≠ 0 := by positivity
  field_simp
  ring

/-- A shifted form of Lemma 2.1: replacing `t` by a smaller vector `s` with `tᵢ - sᵢ ≤ c` costs a
factor `e^c`.  Applied with `sᵢ = ⌊tᵢ⌋` this is the rounding step of Corollary 2.2. -/
theorem lemma_2_1_shift {ε r c : ℝ} {t s : Fin n → ℝ} (hr : 0 < r) (hc : 0 ≤ c) (y : Fin n → ℝ)
    (p : ℤ) {q : Fin n → ℤ} (hq0 : q ≠ 0)
    (hq : |dotProd q y + (p : ℝ)| * PiPlus q ≤ PiPlus q ^ (-ε))
    (hrdef : r ^ (n + 1) = PiPlus q ^ (-ε))
    (ht : ∀ i, max |(q i : ℝ)| 1 = r * Real.exp (t i))
    (hst : ∑ i, s i ≤ ∑ i, t i) (hgap : ∀ i, t i - s i ≤ c) :
    latticeDelta (flowMat s * unipotentMat y) ≤ Real.exp c * r := by
  classical
  set v : Fin (n + 1) → ℤ := Fin.cons p q with hv
  have hvne : v ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i, q i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hq0 (funext hcon)
    intro hcon
    have := congrFun hcon i.succ
    rw [hv] at this
    simp only [Fin.cons_succ, Pi.zero_apply] at this
    exact hi this
  have hcast : (fun i => ((v i : ℤ) : ℝ)) = Fin.cons (p : ℝ) fun i => (q i : ℝ) := by
    funext i
    refine Fin.cases ?_ (fun i' => ?_) i <;> simp [hv]
  have hprod : PiPlus q = r ^ n * Real.exp (∑ i, t i) := by
    rw [PiPlus, Real.exp_sum, Finset.prod_congr rfl fun i _ => ht i, Finset.prod_mul_distrib]
    simp
  have hexp : Real.exp (∑ i, t i) = PiPlus q / r ^ n := by rw [hprod]; field_simp
  have hcr : 0 < Real.exp c * r := by positivity
  have hnorm : ‖(flowMat s * unipotentMat y).mulVec fun i => ((v i : ℤ) : ℝ)‖ ≤ Real.exp c * r := by
    rw [hcast, ← Matrix.mulVec_mulVec, unipotentMat_mulVec, flowMat_mulVec]
    refine (pi_norm_le_iff_of_nonneg hcr.le).mpr fun i => ?_
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp only [Fin.cons_zero, latticeVec, Real.norm_eq_abs, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      have hP : (0:ℝ) < PiPlus q := PiPlus_pos q
      have h1 : |dotProd q y + (p : ℝ)| ≤ PiPlus q ^ (-ε) / PiPlus q := (le_div_iff₀ hP).mpr hq
      have h2 : Real.exp (∑ i, s i) ≤ Real.exp (∑ i, t i) := Real.exp_le_exp.mpr hst
      have hbase : Real.exp (∑ i, t i) * |dotProd q y + (p : ℝ)| ≤ r := by
        calc Real.exp (∑ i, t i) * |dotProd q y + (p : ℝ)|
            ≤ (PiPlus q / r ^ n) * (PiPlus q ^ (-ε) / PiPlus q) := by
              rw [hexp]
              exact mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = PiPlus q ^ (-ε) / r ^ n := by field_simp
          _ = r ^ (n + 1) / r ^ n := by rw [hrdef]
          _ = r := by rw [pow_succ]; field_simp
      have h3 : Real.exp (∑ i, s i) * |dotProd q y + (p : ℝ)| ≤ r :=
        le_trans (mul_le_mul_of_nonneg_right h2 (abs_nonneg _)) hbase
      have h4 : (1:ℝ) ≤ Real.exp c := Real.one_le_exp hc
      nlinarith [h3, h4, hr.le, mul_nonneg (sub_nonneg.mpr h4) hr.le]
    · simp only [Fin.cons_succ, latticeVec, Real.norm_eq_abs, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      have h1 : |(q i' : ℝ)| ≤ r * Real.exp (t i') := by
        rw [← ht i']; exact le_max_left _ _
      calc Real.exp (-(s i')) * |(q i' : ℝ)|
          ≤ Real.exp (-(s i')) * (r * Real.exp (t i')) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = r * Real.exp (t i' - s i') := by
            rw [Real.exp_sub]
            field_simp
            rw [← Real.exp_add]
            simp
        _ ≤ r * Real.exp c := by
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hgap i')) hr.le
        _ = Real.exp c * r := by ring
  exact le_trans (latticeDelta_le _ hvne) hnorm

/-- **Corollary 2.2.**  If `y` is very well multiplicatively approximable then for some `γ > 0`
there are infinitely many `t ∈ ℤ₊ⁿ` with `δ(g_t Λ_y) ≤ e^{-γ t}`. -/
theorem corollary_2_2 (y : Fin n → ℝ) (h : VWMA y) :
    ∃ γ : ℝ, 0 < γ ∧
      {m : Fin n → ℕ | latticeDelta (flowMat (fun i => (m i : ℝ)) * unipotentMat y)
          ≤ Real.exp (-(γ * ∑ i, (m i : ℝ)))}.Infinite := by
  classical
  obtain ⟨ε, hε, hQ⟩ := h
  set γ₀ : ℝ := ε / ((n : ℝ) + 1 + n * ε) with hγ₀
  have hγ₀pos : 0 < γ₀ := by rw [hγ₀]; positivity
  refine ⟨γ₀ / 2, by positivity, ?_⟩
  set M : Set (Fin n → ℕ) :=
    {m : Fin n → ℕ | latticeDelta (flowMat (fun i => (m i : ℝ)) * unipotentMat y)
      ≤ Real.exp (-(γ₀ / 2 * ∑ i, (m i : ℝ)))} with hM
  -- from any `q` with large `Π₊` we manufacture an element of `M` with large coordinate sum
  have hkey : ∀ N : ℝ, ∃ m ∈ M, N < ∑ i, (m i : ℝ) := by
    intro N
    set A : ℝ := max (N + 1) (2 / γ₀) + n with hA
    obtain ⟨q, hqQ, hqM⟩ : ∃ q, q ∈ {q : Fin n → ℤ | ∃ p : ℤ,
        |dotProd q y + (p : ℝ)| * PiPlus q ≤ PiPlus q ^ (-ε)} ∧
        ¬ PiPlus q ≤ Real.exp (A * ((n : ℝ) + 1) / ((n : ℝ) + 1 + n * ε)) := by
      obtain ⟨q, hq⟩ :=
        (hQ.sdiff (finite_PiPlus_le
          (Real.exp (A * ((n : ℝ) + 1) / ((n : ℝ) + 1 + n * ε))))).nonempty
      exact ⟨q, hq.1, hq.2⟩
    obtain ⟨p, hp⟩ := hqQ
    push Not at hqM
    -- basic quantities
    have hPgt : Real.exp (A * ((n : ℝ) + 1) / ((n : ℝ) + 1 + n * ε)) < PiPlus q := hqM
    have hPpos : (0:ℝ) < PiPlus q := PiPlus_pos q
    set L : ℝ := Real.log (PiPlus q) with hL
    have hLge : A * ((n : ℝ) + 1) / ((n : ℝ) + 1 + n * ε) ≤ L := by
      have h2 := Real.log_le_log (Real.exp_pos _) hPgt.le
      rwa [Real.log_exp] at h2
    set t : Fin n → ℝ := expOf ε n q with ht
    set r : ℝ := radiusOf ε n q with hr
    have hTsum : (∑ i, t i) = ((n : ℝ) + 1 + n * ε) / ((n : ℝ) + 1) * L := by
      have h1 := radiusOf_eq_exp_neg_gamma hε n q
      have h2 : radiusOf ε n q = Real.exp (-(ε / ((n:ℝ) + 1)) * L) := rfl
      rw [h2] at h1
      have := Real.exp_injective h1
      have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
      have hn2 : ((n : ℝ) + 1 + n * ε) ≠ 0 := by positivity
      rw [ht]
      field_simp at this ⊢
      nlinarith [this]
    have hTge : A ≤ ∑ i, t i := by
      rw [hTsum]
      have hn1 : (0:ℝ) < (n : ℝ) + 1 := by positivity
      have hn2 : (0:ℝ) < (n : ℝ) + 1 + n * ε := by positivity
      rw [div_le_iff₀ hn2] at hLge
      rw [div_mul_eq_mul_div, le_div_iff₀ hn1]
      nlinarith [hLge]
    have hq0 : q ≠ 0 := by
      intro hcon
      rw [hcon] at hPgt
      have : PiPlus (0 : Fin n → ℤ) = 1 := by simp [PiPlus]
      rw [this] at hPgt
      have : (1:ℝ) ≤ Real.exp (A * ((n : ℝ) + 1) / ((n : ℝ) + 1 + n * ε)) := by
        refine Real.one_le_exp ?_
        have hn2 : (0:ℝ) < (n : ℝ) + 1 + n * ε := by positivity
        have hApos : 0 < A := by
          rw [hA]
          have : 0 < 2 / γ₀ := by positivity
          have h1 : 2 / γ₀ ≤ max (N + 1) (2 / γ₀) := le_max_right _ _
          positivity
        positivity
      linarith
    -- round down
    set m : Fin n → ℕ := fun i => ⌊t i⌋₊ with hm
    have htnn : ∀ i, 0 ≤ t i := fun i => expOf_nonneg hε n q i
    have hmle : ∀ i, ((m i : ℝ)) ≤ t i := fun i => Nat.floor_le (htnn i)
    have hmgap : ∀ i, t i - (m i : ℝ) ≤ 1 := fun i => by
      have := Nat.lt_floor_add_one (t i)
      linarith
    have hsumle : ∑ i, (m i : ℝ) ≤ ∑ i, t i := Finset.sum_le_sum fun i _ => hmle i
    have hsumge : (∑ i, t i) - n ≤ ∑ i, (m i : ℝ) := by
      have : ∑ i, (t i - (m i : ℝ)) ≤ ∑ _i : Fin n, (1:ℝ) := Finset.sum_le_sum fun i _ => hmgap i
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one] at this
      linarith
    have hSge : max (N + 1) (2 / γ₀) ≤ ∑ i, (m i : ℝ) := by
      have : A - n ≤ ∑ i, (m i : ℝ) := by linarith
      rw [hA] at this
      linarith
    refine ⟨m, ?_, ?_⟩
    · -- `m ∈ M`
      have hdelta := lemma_2_1_shift (radiusOf_pos ε n q) zero_le_one y p hq0 hp
        (radiusOf_pow n q) (max_eq_radiusOf_mul_exp ε n q) hsumle hmgap
      have hrexp : r = Real.exp (-(γ₀ * ∑ i, t i)) := radiusOf_eq_exp_neg_gamma hε n q
      have h1 : Real.exp 1 * r ≤ Real.exp (-(γ₀ / 2 * ∑ i, (m i : ℝ))) := by
        rw [hrexp, ← Real.exp_add, Real.exp_le_exp]
        have h2 : γ₀ * ∑ i, (m i : ℝ) ≤ γ₀ * ∑ i, t i :=
          mul_le_mul_of_nonneg_left hsumle hγ₀pos.le
        have h3 : 2 / γ₀ ≤ ∑ i, (m i : ℝ) := le_trans (le_max_right _ _) hSge
        have h4 : 2 ≤ γ₀ * ∑ i, (m i : ℝ) := by
          rw [div_le_iff₀ hγ₀pos] at h3
          linarith
        linarith
      exact le_trans hdelta h1
    · exact lt_of_lt_of_le (by linarith [le_max_left (N + 1) (2 / γ₀)]) hSge
  -- unboundedness of the coordinate sum forces `M` to be infinite
  intro hfin
  obtain ⟨N, hN⟩ := (hfin.image fun m : Fin n → ℕ => ∑ i, (m i : ℝ)).bddAbove
  obtain ⟨m, hmM, hmN⟩ := hkey N
  exact absurd (hN ⟨m, hmM, rfl⟩) (not_le.mpr hmN)

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
