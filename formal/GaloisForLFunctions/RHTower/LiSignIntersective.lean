import GaloisForLFunctions.RHTower.LiSignAlongPolynomials

/-!
# Li's criterion along integer polynomials: the intersective classification

Let `P ∈ ℤ[X]` have positive leading coefficient and degree `≥ 1`. Call `P` *intersective* if it
has a root modulo every positive integer. Say that the index sequence `x ↦ P(x)` *detects* if, for
every family of Cayley roots `v_i` (with the summability and size hypotheses of the paired Li
sums) having a member strictly outside the unit circle, the paired Li sums at `P(x)` are negative
for infinitely many `x`.

**Classification** (`liDetectsAlong_poly_iff_isIntersective`): `x ↦ P(x)` detects iff `P` is
intersective.

* *Intersective ⇒ detects.* For each period `T`, a root `r_T` of `P` modulo `T` gives the index
  family `k ↦ P(Tk + c_T)` with `T ∣ P(Tk + c_T)`. Its phase is a polynomial of degree `deg P`, so
  its Weyl sums are `o(N)` off the roots of unity, and the moment argument of
  `exists_card_filter_seq_gt` applies.
* *Not intersective ⇒ fails.* If `b ∤ P(x)` for all `x`, the Cayley family `2ζ_b^a`
  (`a = 1, …, b−1`) has paired Li sums `2(b−1) + 2ⁿ + 2⁻ⁿ > 0` at every `n = P(x)`.

Consequently, for intersective `P` the Riemann hypothesis holds iff `Re 2λ_{P(x)} ≥ 0` for all
large `x` (`riemannHypothesis_iff_eventually_re_xiLiPaired_intersective`). Examples: `x²`,
`x² − x`, `(x² − 2)(x² − 3)(x² − 6)` are intersective; `x² + 1` (no root mod `3`) and `2x + 1`
(no root mod `2`) are not.
-/

open Complex Filter Finset Polynomial

noncomputable section

namespace RHTower

/-- `P` has a root modulo every positive integer. -/
def IsIntersective (P : ℤ[X]) : Prop := ∀ b : ℕ, 0 < b → ∃ r : ℤ, (b : ℤ) ∣ P.eval r

/-- A polynomial with positive leading coefficient and positive degree eventually exceeds every
bound on the integers. -/
theorem eventually_le_eval_of_leadingCoeff_pos {P : ℤ[X]} (hlc : 0 < P.leadingCoeff)
    (hdeg : 1 ≤ P.natDegree) (B : ℤ) : ∃ X : ℕ, ∀ x : ℤ, (X : ℤ) ≤ x → B ≤ P.eval x := by
  set Q : ℝ[X] := P.map (Int.castRingHom ℝ) with hQ
  have hinj : Function.Injective (Int.castRingHom ℝ) := Int.cast_injective
  have hQdeg : 0 < Q.degree := by
    rw [← natDegree_pos_iff_degree_pos, hQ, natDegree_map_eq_of_injective hinj]; omega
  have hQlc : 0 ≤ Q.leadingCoeff := by
    rw [hQ, leadingCoeff_map_of_injective hinj]
    have : (0 : ℝ) < (P.leadingCoeff : ℝ) := by exact_mod_cast hlc
    simpa using this.le
  have ht := tendsto_atTop_of_leadingCoeff_nonneg Q hQdeg hQlc
  obtain ⟨Y, hY⟩ := Filter.eventually_atTop.mp (ht.eventually_ge_atTop (B : ℝ))
  obtain ⟨X, hX⟩ := exists_nat_ge Y
  refine ⟨X, fun x hx => ?_⟩
  have h1 := hY (x : ℝ) (le_trans hX (by exact_mod_cast hx))
  rw [hQ, eval_intCast_map] at h1
  simp only [eq_intCast, Int.cast_id] at h1
  exact_mod_cast h1

/-- An affine substitution `x ↦ ax + c`, `a ≠ 0`, keeps a polynomial phase of degree `deg Q`. -/
theorem constDiffPhase_comp_linear {Q : ℤ[X]} (hdeg : 1 ≤ Q.natDegree) {a c : ℤ} (ha : a ≠ 0) :
    ConstDiffPhase Q.natDegree (fun x : ℤ => (Q.comp (C a * X + C c)).eval x) := by
  set R : ℤ[X] := Q.comp (C a * X + C c) with hR
  have hlin : (C a * X + C c).natDegree = 1 := natDegree_linear ha
  have hdegR : R.natDegree = Q.natDegree := by rw [hR, natDegree_comp, hlin, mul_one]
  have hQ : Q ≠ 0 := by rintro rfl; simp at hdeg
  have hlcR : R.leadingCoeff ≠ 0 := by
    rw [hR, leadingCoeff_comp (by rw [hlin]; norm_num), leadingCoeff_linear ha]
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr hQ) (pow_ne_zero _ ha)
  refine ⟨R.leadingCoeff * (Q.natDegree.factorial : ℤ),
    mul_ne_zero hlcR (by exact_mod_cast (Nat.factorial_pos _).ne'), fun n => ?_⟩
  have := congrFun (fwdDiff_iter_degree_eq_factorial R) n
  rw [hdegR] at this
  rw [this, Pi.smul_apply, Pi.natCast_apply, smul_eq_mul]

theorem eval_comp_linear (P : ℤ[X]) (a c x : ℤ) :
    (P.comp (C a * X + C c)).eval x = P.eval (a * x + c) := by
  simp [eval_comp]

theorem leadingCoeff_comp_linear_pos {P : ℤ[X]} (hlc : 0 < P.leadingCoeff) {a : ℤ} (ha : 0 < a)
    (c : ℤ) : 0 < (P.comp (C a * X + C c)).leadingCoeff := by
  have hlin : (C a * X + C c).natDegree = 1 := natDegree_linear ha.ne'
  rw [leadingCoeff_comp (by rw [hlin]; norm_num), leadingCoeff_linear ha.ne']
  positivity

theorem natDegree_comp_linear (P : ℤ[X]) {a : ℤ} (ha : a ≠ 0) (c : ℤ) :
    (P.comp (C a * X + C c)).natDegree = P.natDegree := by
  rw [natDegree_comp, natDegree_linear ha, mul_one]

/-! ## Intersective polynomials detect -/

/-- For `T > 0` an intersective `P` has a shift `c` with `T ∣ P(c)` and `P(Tk + c) ≥ 0` for all
`k ≥ 0`. -/
theorem exists_intersective_index {P : ℤ[X]} (hP : IsIntersective P) (hlc : 0 < P.leadingCoeff)
    (hdeg : 1 ≤ P.natDegree) {T : ℕ} (hT : 0 < T) :
    ∃ c : ℤ, (T : ℤ) ∣ P.eval c ∧ ∀ k : ℕ, 0 ≤ P.eval ((T : ℤ) * k + c) := by
  obtain ⟨r, hr⟩ := hP T hT
  have hTz : (0 : ℤ) < T := by exact_mod_cast hT
  obtain ⟨X₀, hX₀⟩ := eventually_le_eval_of_leadingCoeff_pos (P := P.comp (C (T : ℤ) * X + C r))
    (leadingCoeff_comp_linear_pos hlc hTz r)
    (by rw [natDegree_comp_linear P hTz.ne']; exact hdeg) 0
  refine ⟨(T : ℤ) * X₀ + r, ?_, fun k => ?_⟩
  · have h1 := sub_dvd_eval_sub ((T : ℤ) * X₀ + r) r P
    have h2 : (T : ℤ) ∣ ((T : ℤ) * X₀ + r) - r := ⟨X₀, by ring⟩
    have := dvd_add (dvd_trans h2 h1) hr
    simpa using this
  · have hk : (0 : ℤ) ≤ k := Nat.cast_nonneg k
    have := hX₀ ((k : ℤ) + X₀) (by linarith)
    rw [eval_comp_linear] at this
    have e : (T : ℤ) * (k + X₀) + r = (T : ℤ) * k + ((T : ℤ) * X₀ + r) := by ring
    rwa [e] at this

/-- **Intersective polynomials detect, abstract form.** If one member of the family lies strictly
outside the unit circle, the paired Li sums at `P(x)` are negative for infinitely many `x`. -/
theorem frequently_poly_re_tsum_liTerm_neg {P : ℤ[X]} (hP : IsIntersective P)
    (hlc : 0 < P.leadingCoeff) (hdeg : 1 ≤ P.natDegree) {ι : Type*} {v : ι → ℂ} {m : ι → ℝ}
    {M : ℝ} (hm : ∀ i, 1 ≤ m i) (hv : ∀ i, 1 ≤ ‖v i‖) (hM : ∀ i, ‖v i‖ ≤ M)
    (hs : Summable fun i => m i * ‖v i - 1‖ ^ (2 : ℕ)) {i₀ : ι} (hlt : 1 < ‖v i₀‖) :
    ∃ᶠ x : ℕ in atTop, ∑' i, m i * (liTerm (v i) (P.eval (x : ℤ)).toNat).re < 0 := by
  classical
  have hidx : ∀ T : ℕ, 0 < T → ∃ c : ℤ, (T : ℤ) ∣ P.eval c ∧
      ∀ k : ℕ, 0 ≤ P.eval ((T : ℤ) * k + c) :=
    fun T hT => exists_intersective_index hP hlc hdeg hT
  choose c hcdvd hcnn using hidx
  set s : ℕ → ℕ → ℕ := fun T k =>
    if h : 0 < T then (P.eval ((T : ℤ) * k + c T h)).toNat else 0 with hsdef
  have hseval : ∀ T (hT : 0 < T) (k : ℕ), ((s T k : ℕ) : ℤ) = P.eval ((T : ℤ) * k + c T hT) := by
    intro T hT k
    simp only [hsdef, dif_pos hT]
    exact Int.toNat_of_nonneg (hcnn T hT k)
  have hdiv : ∀ T k, T ∣ s T k := by
    intro T k
    by_cases hT : 0 < T
    · rw [← Int.natCast_dvd_natCast, hseval T hT k]
      have h1 := sub_dvd_eval_sub ((T : ℤ) * k + c T hT) (c T hT) P
      have h2 : (T : ℤ) ∣ ((T : ℤ) * k + c T hT) - c T hT := ⟨k, by ring⟩
      have := dvd_add (dvd_trans h2 h1) (hcdvd T hT)
      simpa using this
    · simp only [hsdef, dif_neg hT]
      exact dvd_zero T
  have hweyl : ∀ T : ℕ, 0 < T → ∀ w : ℂ, ‖w‖ = 1 → (∀ n : ℕ, 0 < n → w ^ n ≠ 1) →
      ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ‖∑ k ∈ range N, w ^ (s T k)‖ ≤ δ * N := by
    intro T hT w hw hroot δ hδ
    have hTz : (T : ℤ) ≠ 0 := by exact_mod_cast hT.ne'
    obtain ⟨N₀, hN₀⟩ := eventually_norm_sum_zpow_le P.natDegree hdeg
      (constDiffPhase_comp_linear hdeg (c := c T hT) hTz) hw hroot hδ
    refine ⟨N₀, fun N hN => ?_⟩
    have e : ∀ k : ℕ, w ^ (s T k) = w ^ ((P.comp (C (T : ℤ) * X + C (c T hT))).eval (k : ℤ)) := by
      intro k
      rw [eval_comp_linear, ← hseval T hT k, zpow_natCast]
    rw [Finset.sum_congr rfl fun k _ => e k]
    exact hN₀ N hN
  obtain ⟨D, R, hDne, hR1, hDnorm, hdec⟩ := abs_re_tsum_liTerm_add_dominant_le hm hv hM hs hlt
  have hR0 : (0 : ℝ) < R := by linarith
  haveI : Nonempty {x // x ∈ D} := ⟨⟨hDne.choose, hDne.choose_spec⟩⟩
  set u : {x // x ∈ D} → ℂ := fun i => v i / R with hudef
  have hunit : ∀ i, ‖u i‖ = 1 := by
    intro i
    rw [hudef]; simp only
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0, (hDnorm i).mp i.2,
      div_self hR0.ne']
  obtain ⟨T, hT, ε, cc, hε, hcc, N₀, hcount⟩ :=
    exists_card_filter_seq_gt s hdiv hweyl u (fun i => m i) hunit (fun i => by linarith [hm i])
  obtain ⟨N₁, hN₁⟩ := hdec (ε / 2) (by linarith)
  have hf : ∀ n, ∑ i : {x // x ∈ D}, m i * (u i ^ n).re = ∑ i ∈ D, m i * ((v i / R) ^ n).re :=
    fun n => Finset.sum_coe_sort D (fun i => m i * ((v i / R) ^ n).re)
  obtain ⟨Y, hY⟩ := eventually_le_eval_of_leadingCoeff_pos hlc hdeg (N₁ : ℤ)
  rw [Filter.frequently_atTop]
  intro x₀
  set A : ℕ := x₀ + Y + (c T hT).natAbs with hA
  obtain ⟨N, hN⟩ := exists_nat_gt (((A : ℝ) + 1) / cc + N₀)
  have hNN₀ : N₀ ≤ N := by
    have : (N₀ : ℝ) < N := by
      have : (0 : ℝ) ≤ ((A : ℝ) + 1) / cc := by positivity
      linarith
    exact_mod_cast this.le
  have h1 := hcount N hNN₀
  have hbig : A < ((range N).filter
      (fun k => ε < ∑ i : {x // x ∈ D}, m i * (u i ^ (s T k)).re)).card := by
    have h2 : (A : ℝ) + 1 < cc * N := by
      have : ((A : ℝ) + 1) / cc < N := by
        have : (0 : ℝ) ≤ (N₀ : ℝ) := Nat.cast_nonneg _
        linarith
      rwa [div_lt_iff₀ hcc, mul_comm] at this
    have : (A : ℝ) < (((range N).filter
        (fun k => ε < ∑ i : {x // x ∈ D}, m i * (u i ^ (s T k)).re)).card : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨k, hk, hkA⟩ : ∃ k ∈ (range N).filter (fun k => ε < ∑ i : {x // x ∈ D}, m i * (u i ^ (s T k)).re),
      A ≤ k := by
    by_contra hno
    push Not at hno
    have hsub : (range N).filter (fun k => ε < ∑ i : {x // x ∈ D}, m i * (u i ^ (s T k)).re) ⊆ range A :=
      fun k hk => mem_range.mpr (hno k hk)
    have := card_le_card hsub
    rw [card_range] at this
    omega
  have hP' := (mem_filter.mp hk).2
  have hT1 : (1 : ℤ) ≤ T := by exact_mod_cast hT
  have hk0 : (0 : ℤ) ≤ k := Nat.cast_nonneg k
  have hkA' : (A : ℤ) ≤ k := by exact_mod_cast hkA
  have hcabs : -((c T hT).natAbs : ℤ) ≤ c T hT := by
    have := Int.natCast_natAbs (c T hT)
    have := neg_abs_le (c T hT)
    rw [Int.natCast_natAbs] at *
    linarith
  have hTk : (k : ℤ) ≤ (T : ℤ) * k := by nlinarith
  have harg : ((x₀ + Y : ℕ) : ℤ) ≤ (T : ℤ) * k + c T hT := by
    have : (A : ℤ) = ((x₀ + Y : ℕ) : ℤ) + ((c T hT).natAbs : ℤ) := by rw [hA]; push_cast; ring
    linarith
  set x : ℕ := ((T : ℤ) * k + c T hT).toNat with hxdef
  have hx : (x : ℤ) = (T : ℤ) * k + c T hT :=
    Int.toNat_of_nonneg (le_trans (by positivity) harg)
  refine ⟨x, ?_, ?_⟩
  · have : ((x₀ : ℕ) : ℤ) ≤ (x : ℤ) := by rw [hx]; push_cast at harg; linarith
    exact_mod_cast this
  · have hidx_eq : (P.eval (x : ℤ)).toNat = s T k := by
      rw [hx]; simp [hsdef, dif_pos hT]
    rw [hidx_eq]
    have hn : N₁ ≤ s T k := by
      have h2 := hY ((T : ℤ) * k + c T hT) (by push_cast at harg; linarith)
      rw [← hseval T hT k] at h2
      exact_mod_cast h2
    have hd := hN₁ _ hn
    rw [hf] at hP'
    have hRn : (0 : ℝ) < R ^ (s T k) := pow_pos hR0 _
    have h2 := (abs_le.mp hd).2
    have h3 := mul_pos hRn (sub_pos.mpr hP')
    nlinarith

/-! ## The classification -/

/-- The index sequence `s` *detects*: for every family of Cayley roots with a member strictly
outside the unit circle, the paired Li sums at `s x` are negative for infinitely many `x`. -/
def LiDetectsAlong (s : ℕ → ℕ) : Prop :=
  ∀ (ι : Type) (v : ι → ℂ) (m : ι → ℝ) (M : ℝ), (∀ i, 1 ≤ m i) → (∀ i, 1 ≤ ‖v i‖) →
    (∀ i, ‖v i‖ ≤ M) → Summable (fun i => m i * ‖v i - 1‖ ^ (2 : ℕ)) →
    ∀ i₀ : ι, 1 < ‖v i₀‖ → ∃ᶠ x in atTop, ∑' i, m i * (liTerm (v i) (s x)).re < 0

/-- **The intersective classification.** For `P ∈ ℤ[X]` with positive leading coefficient and
degree `≥ 1`, the index sequence `x ↦ P(x)` detects iff `P` has a root modulo every positive
integer. -/
theorem liDetectsAlong_poly_iff_isIntersective {P : ℤ[X]} (hlc : 0 < P.leadingCoeff)
    (hdeg : 1 ≤ P.natDegree) :
    LiDetectsAlong (fun x => (P.eval (x : ℤ)).toNat) ↔ IsIntersective P := by
  classical
  constructor
  · intro hdet
    by_contra hnot
    simp only [IsIntersective] at hnot
    push Not at hnot
    obtain ⟨b, hb, hnd⟩ := hnot
    have hb2 : 2 ≤ b := by
      by_contra h
      have hb1 : b = 1 := by omega
      subst hb1
      exact hnd 0 (by simp)
    have hprim : IsPrimitiveRoot (primitiveRootExp b) b :=
      Complex.isPrimitiveRoot_exp b (by omega)
    have hnorm : ‖primitiveRootExp b‖ = 1 := hprim.norm'_eq_one (by omega)
    let v : {a // a ∈ Ico 1 b} → ℂ := fun a => ((2 : ℝ) : ℂ) * primitiveRootExp b ^ a.1
    have hv2 : ∀ a, ‖v a‖ = 2 := fun a => by
      simp only [v, norm_mul, norm_pow, hnorm, one_pow, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      norm_num
    have h1mem : (1 : ℕ) ∈ Ico 1 b := mem_Ico.mpr ⟨le_rfl, by omega⟩
    have hfreq := hdet {a // a ∈ Ico 1 b} v (fun _ => 1) 2 (fun _ => le_rfl)
      (fun a => by rw [hv2]; norm_num) (fun a => by rw [hv2]) (Summable.of_finite)
      ⟨1, h1mem⟩ (by rw [hv2]; norm_num)
    obtain ⟨X₀, hX₀⟩ := eventually_le_eval_of_leadingCoeff_pos hlc hdeg 0
    have hev : ∀ᶠ x : ℕ in atTop,
        ¬ (∑' i, (fun _ => (1 : ℝ)) i * (liTerm (v i) ((P.eval (x : ℤ)).toNat)).re < 0) := by
      refine Filter.eventually_atTop.mpr ⟨X₀, fun x hx => ?_⟩
      have hnn : 0 ≤ P.eval (x : ℤ) := hX₀ _ (by exact_mod_cast hx)
      have hndiv : ¬ b ∣ (P.eval (x : ℤ)).toNat := by
        intro h
        apply hnd (x : ℤ)
        rw [← Int.toNat_of_nonneg hnn]
        exact_mod_cast h
      rw [tsum_fintype]
      have hpos := re_sum_liTerm_rootFamily_pos hb2 hndiv (R := 2) (by norm_num)
      have e : ∑ i, (fun _ => (1 : ℝ)) i * (liTerm (v i) ((P.eval (x : ℤ)).toNat)).re =
          ∑ a ∈ Ico 1 b, (liTerm (((2 : ℝ) : ℂ) * primitiveRootExp b ^ a)
            ((P.eval (x : ℤ)).toNat)).re := by
        simp only [one_mul, v]
        exact Finset.sum_coe_sort (Ico 1 b)
          (fun a => (liTerm (((2 : ℝ) : ℂ) * primitiveRootExp b ^ a)
            ((P.eval (x : ℤ)).toNat)).re)
      rw [e]
      exact not_lt.mpr hpos.le
    obtain ⟨x, hx1, hx2⟩ := (hfreq.and_eventually hev).exists
    exact hx2 hx1
  · intro hP ι v m M hm hv hM hs i₀ hlt
    exact frequently_poly_re_tsum_liTerm_neg hP hlc hdeg hm hv hM hs hlt

/-- **Li's criterion along an intersective polynomial.** -/
theorem riemannHypothesis_iff_eventually_re_xiLiPaired_intersective {P : ℤ[X]}
    (hP : IsIntersective P) (hlc : 0 < P.leadingCoeff) (hdeg : 1 ≤ P.natDegree) :
    RiemannHypothesis ↔ ∀ᶠ x : ℕ in atTop, 0 ≤ (xiLiPaired (P.eval (x : ℤ)).toNat).re := by
  constructor
  · intro hRH
    exact Filter.Eventually.of_forall fun x => re_xiLiPaired_nonneg_of_rh hRH _
  · intro h
    by_contra hRH
    obtain ⟨M, hmult, hvnorm, hvM, hsum, _, hbad⟩ := xiLi_family_facts
    obtain ⟨ρ₀, hρ₀⟩ := hbad hRH
    have hfreq := frequently_poly_re_tsum_liTerm_neg hP hlc hdeg hmult hvnorm hvM hsum hρ₀
    obtain ⟨x, hx1, hx2⟩ := (hfreq.and_eventually h).exists
    rw [← re_xiLiPaired_eq_tsum_mult] at hx1
    linarith

/-! ## Examples -/

theorem isIntersective_of_eval_zero {P : ℤ[X]} (h : P.eval 0 = 0) : IsIntersective P :=
  fun _ _ => ⟨0, by rw [h]; exact dvd_zero _⟩

/-- `x² + 1` has no root modulo `3`, so it is not intersective. -/
theorem not_isIntersective_X_sq_add_one : ¬ IsIntersective (X ^ 2 + 1 : ℤ[X]) := by
  intro h
  obtain ⟨r, hr⟩ := h 3 (by norm_num)
  have h3 : ((r ^ 2 + 1 : ℤ) : ZMod 3) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa using hr
  push_cast at h3
  revert h3
  generalize (r : ZMod 3) = z
  revert z
  decide

/-! ## Two-sided obstruction: odd roots of unity -/

theorem re_liTerm_ofReal_mul_unit {z : ℂ} (hz : ‖z‖ = 1) {R : ℝ} (hR : 0 < R) (n : ℕ) :
    (liTerm ((R : ℂ) * z) n).re = 2 - (R ^ n + (R⁻¹) ^ n) * (z ^ n).re := by
  have hinv : z⁻¹ = (starRingEnd ℂ) z := (conj_eq_inv_of_unit_norm hz).symm
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  unfold liTerm
  rw [mul_inv, hinv, mul_pow, mul_pow, ← map_pow]
  simp only [Complex.sub_re, Complex.re_ofNat]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_inv, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul, Complex.conj_re]
  ring

/-- **The odd-root family is invisible off the multiples of `b`.** With `ω = e^{πi/b}` and any
`R > 0`, the Cayley family `Rω^{2j+1}` (`j < b`) has paired Li sum exactly `2b` at every index `n`
with `b ∤ n`. -/
theorem sum_re_liTerm_oddRootFamily_eq {b n : ℕ} (hb : 1 ≤ b) (hn : ¬ b ∣ n) {R : ℝ}
    (hR : 0 < R) :
    ∑ j ∈ range b, (liTerm ((R : ℂ) * primitiveRootExp (2 * b) ^ (2 * j + 1)) n).re =
      2 * b := by
  have hprim : IsPrimitiveRoot (primitiveRootExp (2 * b)) (2 * b) :=
    Complex.isPrimitiveRoot_exp (2 * b) (by omega)
  have hnorm : ‖primitiveRootExp (2 * b)‖ = 1 := hprim.norm'_eq_one (by omega)
  set ω := primitiveRootExp (2 * b) with hω
  have hunit : ∀ j : ℕ, ‖ω ^ (2 * j + 1)‖ = 1 := fun j => by rw [norm_pow, hnorm, one_pow]
  -- the odd-index geometric sum vanishes
  have hx1 : ω ^ (2 * n) ≠ 1 := by
    intro h
    have := (hprim.pow_eq_one_iff_dvd (2 * n)).mp h
    exact hn (Nat.dvd_of_mul_dvd_mul_left (by norm_num) this)
  have hxb : (ω ^ (2 * n)) ^ b = 1 := by
    rw [← pow_mul, show 2 * n * b = 2 * b * n by ring, pow_mul, hprim.pow_eq_one, one_pow]
  have hgeom : ∑ j ∈ range b, (ω ^ (2 * n)) ^ j = 0 := by
    rw [geom_sum_eq hx1, hxb, sub_self, zero_div]
  have hodd : ∑ j ∈ range b, ((ω ^ (2 * j + 1)) ^ n).re = 0 := by
    rw [← Complex.re_sum]
    have e : ∑ j ∈ range b, (ω ^ (2 * j + 1)) ^ n = ω ^ n * ∑ j ∈ range b, (ω ^ (2 * n)) ^ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      ring
    rw [e, hgeom, mul_zero, Complex.zero_re]
  rw [Finset.sum_congr rfl fun j _ => re_liTerm_ofReal_mul_unit (hunit j) hR n,
    Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul, ← Finset.mul_sum, hodd]
  ring

/-- **Both sides of the Li pinning hold along a sequence avoiding `0 mod b`, for a family with
roots outside the unit circle.** For `b ≥ 2` and `R > 1` the odd-root family has paired sums
`0 ≤ 2b ≤ n²·2b` at every index `n ≥ 1` with `b ∤ n`, and its first paired sum is also `2b`. -/
theorem oddRootFamily_pinned {b n : ℕ} (hb : 2 ≤ b) (hn : ¬ b ∣ n) (hn1 : 1 ≤ n) {R : ℝ}
    (hR : 1 < R) :
    0 ≤ ∑ j ∈ range b, (liTerm ((R : ℂ) * primitiveRootExp (2 * b) ^ (2 * j + 1)) n).re ∧
      ∑ j ∈ range b, (liTerm ((R : ℂ) * primitiveRootExp (2 * b) ^ (2 * j + 1)) n).re ≤
        (n : ℝ) ^ 2 * ∑ j ∈ range b,
          (liTerm ((R : ℂ) * primitiveRootExp (2 * b) ^ (2 * j + 1)) 1).re := by
  have hR0 : 0 < R := by linarith
  have h1 : ¬ b ∣ 1 := fun h => by have := Nat.le_of_dvd one_pos h; omega
  rw [sum_re_liTerm_oddRootFamily_eq (by omega) hn hR0,
    sum_re_liTerm_oddRootFamily_eq (by omega) h1 hR0]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  constructor
  · positivity
  · have := mul_le_mul_of_nonneg_right hsq (by positivity : (0 : ℝ) ≤ 2 * b)
    linarith

end RHTower

end
