import GaloisForLFunctions.FiniteFreeProbability.WalshHalfPlaneTheorem
import GaloisForLFunctions.FiniteFreeProbability.DirichletPiecesAreNeverRealRooted

/-!
# Hermite–Biehler stability of normalized Euler factors

In the critical direction `s = σ + iw` the Euler factor `1 − p^{−s}` is
`p^{−iw/2} (p^{iw/2} − q p^{−iw/2})` with `q = p^{−σ}`. Its normalized form
`g(w) = e^{cw} − q e^{−cw}`, `c = i ℓ/2`, `ℓ = log p`, has reversed Jensen polynomials

`R_d(g) = (X + c)^d − q (X − c)^d`,

whose roots satisfy `|x + c| < |x − c|` (an Apollonius circle): all of them lie in the open lower
half-plane, at every degree `d`, for every `0 ≤ q < 1`. By Walsh's theorem the finite free
convolution of such pieces, which is the reversed Jensen polynomial of the finite normalized Euler
product `G_S = Π_{p ∈ S} g_p`, keeps all roots in the open lower half-plane. The polynomial
Hermite–Biehler theorem then makes the functional-equation symmetrization
`R_d(G_S) + R_d(G_S)^#` real-rooted, at every degree, for every `σ > 0` (inside the critical strip
included) and every finite set of primes.

The normalization costs the translation `X ↦ X + iℓ/2` per prime: without it the roots of
`R_d(1 − q e^{−iℓw})` only satisfy `Im x < ℓ/2`, and the Walsh bound for `Π_{p ∈ S}` drifts to
`Im x < Σ_{p∈S} log p / 2`.
-/

open Polynomial Complex
open scoped ComplexConjugate

namespace FiniteFreeProbability

noncomputable section

/-! ## Linearity of the reversed Jensen polynomial -/

section Linear

variable {K : Type*} [Field K]

theorem diffOp_sub_left (h₁ h₂ p : K[X]) : diffOp (h₁ - h₂) p = diffOp h₁ p - diffOp h₂ p := by
  simp [diffOp]

theorem diffOp_C_mul_left (a : K) (h p : K[X]) : diffOp (C a * h) p = C a * diffOp h p := by
  rw [diffOp_mul]
  simp [diffOp, Module.algebraMap_end_apply, smul_eq_C_mul]

theorem jensenRev_sub (d : ℕ) (f g : PowerSeries K) :
    jensenRev d (f - g) = jensenRev d f - jensenRev d g := by
  simp only [jensenRev, map_sub, diffOp_sub_left]

theorem jensenRev_C_mul (d : ℕ) (a : K) (f : PowerSeries K) :
    jensenRev d (PowerSeries.C a * f) = C a * jensenRev d f := by
  rw [jensenRev, PowerSeries.trunc_C_mul, diffOp_C_mul_left, jensenRev]

theorem jensenRev_one (d : ℕ) : jensenRev d (1 : PowerSeries K) = X ^ d := by
  rw [jensenRev, diffOp_congr (h' := 1) (natDegree_X_pow_le d)]
  · simp [diffOp]
  · intro i hi
    rw [PowerSeries.coeff_trunc, if_pos (by omega), PowerSeries.coeff_one, coeff_one]

/-- The top coefficient of `R_d(f)` is `f(0)`. -/
theorem coeff_jensenRev_self (d : ℕ) (f : PowerSeries K) :
    (jensenRev d f).coeff d = PowerSeries.constantCoeff f := by
  rw [jensenRev_eq_sum, finsetSum_coeff, Finset.sum_eq_single 0]
  · simp
  · intro i hi hi0
    have : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.succ_pos d)) h

theorem natDegree_jensenRev {d : ℕ} {f : PowerSeries K} (hf : PowerSeries.constantCoeff f ≠ 0) :
    (jensenRev d f).natDegree = d :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_jensenRev_le d f)
    (by rwa [coeff_jensenRev_self])

theorem jensenRev_ne_zero {d : ℕ} {f : PowerSeries K} (hf : PowerSeries.constantCoeff f ≠ 0) :
    jensenRev d f ≠ 0 := fun h => hf (by rw [← coeff_jensenRev_self d f, h, coeff_zero])

end Linear

/-! ## The normalized Euler factor and its Apollonius circle -/

/-- The normalized Euler factor `e^{cw} − q e^{−cw}`. -/
def eulerFactor (q c : ℂ) : PowerSeries ℂ :=
  expSeries c - PowerSeries.C q * expSeries (-c)

theorem constantCoeff_expSeries (c : ℂ) : PowerSeries.constantCoeff (expSeries c) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, expSeries, PowerSeries.coeff_mk]
  simp

theorem constantCoeff_eulerFactor (q c : ℂ) : PowerSeries.constantCoeff (eulerFactor q c) = 1 - q := by
  rw [eulerFactor, map_sub, map_mul, PowerSeries.constantCoeff_C, constantCoeff_expSeries,
    constantCoeff_expSeries, mul_one]

theorem jensenRev_eulerFactor (d : ℕ) (q c : ℂ) :
    jensenRev d (eulerFactor q c) = (X + C c) ^ d - C q * (X - C c) ^ d := by
  rw [eulerFactor, jensenRev_sub, jensenRev_C_mul, expSeries, expSeries, jensenRev_exp,
    jensenRev_exp, map_neg, ← sub_eq_add_neg]

/-- **Apollonius.** For `‖q‖ < 1` and `c ≠ 0`, every root of `(X + c)^d − q (X − c)^d` is strictly
closer to `−c` than to `c`. -/
theorem norm_add_lt_norm_sub_of_isRoot {q c x : ℂ} (hq : ‖q‖ < 1) (hc : c ≠ 0) {d : ℕ}
    (hd : 1 ≤ d) (hx : ((X + C c) ^ d - C q * (X - C c) ^ d).IsRoot x) : ‖x + c‖ < ‖x - c‖ := by
  have hx' : (x + c) ^ d = q * (x - c) ^ d := by
    have := hx; simp only [IsRoot, eval_sub, eval_mul, eval_pow, eval_add, eval_X, eval_C] at this
    exact sub_eq_zero.1 this
  have hxc : x - c ≠ 0 := by
    intro h0
    have hx0 : x = c := sub_eq_zero.1 h0
    rw [h0, zero_pow (by omega), mul_zero, hx0] at hx'
    exact hc (by have := pow_eq_zero_iff (n := d) (by omega) |>.1 hx'; linear_combination this / 2)
  have hn : ‖x + c‖ ^ d < ‖x - c‖ ^ d := by
    rw [← norm_pow, hx', norm_mul, norm_pow]
    exact mul_lt_of_lt_one_left (by positivity) hq
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by omega)).1 hn

/-- `‖x + iℓ/2‖ < ‖x − iℓ/2‖` is the open lower half-plane. -/
theorem im_neg_of_norm_add_lt {ℓ : ℝ} (hℓ : 0 < ℓ) {x : ℂ}
    (h : ‖x + I * (ℓ / 2 : ℝ)‖ < ‖x - I * (ℓ / 2 : ℝ)‖) : x.im < 0 := by
  have h2 := (pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).2 h
  rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply] at h2
  simp at h2
  nlinarith

/-- **Normalized Euler factors are Hermite–Biehler stable at every degree.** -/
theorem im_neg_of_isRoot_jensenRev_eulerFactor {q : ℂ} (hq : ‖q‖ < 1) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {d : ℕ} (hd : 1 ≤ d) {x : ℂ}
    (hx : (jensenRev d (eulerFactor q (I * (ℓ / 2 : ℝ)))).IsRoot x) : x.im < 0 := by
  rw [jensenRev_eulerFactor] at hx
  refine im_neg_of_norm_add_lt hℓ (norm_add_lt_norm_sub_of_isRoot hq ?_ hd hx)
  exact mul_ne_zero I_ne_zero (by exact_mod_cast (by linarith : (ℓ / 2 : ℝ) ≠ 0))

/-! ## Walsh with a strict half-plane -/

/-- Strict form of Walsh's theorem: roots of `p` in `Im < a`, roots of `q` in `Im ≤ b`. -/
theorem ffConv_root_im_lt {d : ℕ} {p q : ℂ[X]} (hp0 : p ≠ 0) (hp : p.natDegree = d)
    (hq0 : q ≠ 0) (hq : q.natDegree ≤ d) {a b : ℝ} (hpa : ∀ r, p.IsRoot r → r.im < a)
    (hqb : ∀ μ, q.IsRoot μ → μ.im ≤ b) {z : ℂ} (hz : (ffConv d p q).IsRoot z) : z.im < a + b := by
  classical
  by_cases hT : (p.roots.map Complex.im).toFinset.Nonempty
  · set m := (p.roots.map Complex.im).toFinset.max' hT
    have hm : m < a := by
      obtain ⟨r, hr, hrm⟩ := Multiset.mem_map.1
        (Multiset.mem_toFinset.1 (Finset.max'_mem _ hT))
      rw [show m = r.im from hrm.symm]; exact hpa r ((mem_roots hp0).1 hr)
    have hle : ∀ r, p.IsRoot r → r.im ≤ m := fun r hr =>
      Finset.le_max' _ _ (Multiset.mem_toFinset.2 (Multiset.mem_map_of_mem _ ((mem_roots hp0).2 hr)))
    have := ffConv_root_im_le hp0 hp hq0 hq hle hqb hz
    linarith
  · have hnone : ∀ r, ¬ p.IsRoot r := fun r hr =>
      hT ⟨r.im, Multiset.mem_toFinset.2 (Multiset.mem_map_of_mem _ ((mem_roots hp0).2 hr))⟩
    have := ffConv_root_im_le (a := a - 1) hp0 hp hq0 hq (fun r hr => absurd hr (hnone r)) hqb hz
    linarith

/-! ## Finite normalized Euler products -/

/-- The finite normalized Euler product `Π_{i ∈ S} (e^{iℓ_i w/2} − q_i e^{−iℓ_i w/2})`. -/
def eulerProduct {ι : Type*} (S : Finset ι) (q : ι → ℂ) (ℓ : ι → ℝ) : PowerSeries ℂ :=
  ∏ i ∈ S, eulerFactor (q i) (I * (ℓ i / 2 : ℝ))

theorem constantCoeff_eulerProduct_ne_zero {ι : Type*} (S : Finset ι) (q : ι → ℂ) (ℓ : ι → ℝ)
    (hq : ∀ i ∈ S, ‖q i‖ < 1) : PowerSeries.constantCoeff (eulerProduct S q ℓ) ≠ 0 := by
  rw [eulerProduct, map_prod]
  refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
  rw [constantCoeff_eulerFactor, sub_ne_zero]
  intro h
  have := hq i hi
  rw [← h, norm_one] at this
  exact lt_irrefl _ this

/-- **Walsh for Euler products.** The reversed Jensen polynomials of a finite normalized Euler
product have all roots in `Im ≤ 0`, and in `Im < 0` as soon as the product is nonempty. -/
theorem roots_jensenRev_eulerProduct {ι : Type*} [DecidableEq ι] (q : ι → ℂ) (ℓ : ι → ℝ)
    {d : ℕ} (hd : 1 ≤ d) (S : Finset ι) (hq : ∀ i ∈ S, ‖q i‖ < 1) (hℓ : ∀ i ∈ S, 0 < ℓ i) :
    (∀ x, (jensenRev d (eulerProduct S q ℓ)).IsRoot x → x.im ≤ 0) ∧
      (S.Nonempty → ∀ x, (jensenRev d (eulerProduct S q ℓ)).IsRoot x → x.im < 0) := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨fun x hx => ?_, fun h => absurd h Finset.not_nonempty_empty⟩
    rw [eulerProduct, Finset.prod_empty, jensenRev_one] at hx
    have hx' := hx
    simp [IsRoot] at hx'
    simp [hx'.1]
  | insert a S ha ih =>
    have hqS : ∀ i ∈ S, ‖q i‖ < 1 := fun i hi => hq i (Finset.mem_insert_of_mem hi)
    have hℓS : ∀ i ∈ S, 0 < ℓ i := fun i hi => hℓ i (Finset.mem_insert_of_mem hi)
    obtain ⟨ihc, -⟩ := ih hqS hℓS
    have hqa := hq a (Finset.mem_insert_self a S)
    have hℓa := hℓ a (Finset.mem_insert_self a S)
    have hfa : PowerSeries.constantCoeff (eulerFactor (q a) (I * (ℓ a / 2 : ℝ))) ≠ 0 := by
      have := constantCoeff_eulerProduct_ne_zero {a} q ℓ (by simpa using hqa)
      simpa [eulerProduct] using this
    have hF := constantCoeff_eulerProduct_ne_zero S q ℓ hqS
    have hstrict : ∀ x, (jensenRev d (eulerProduct (insert a S) q ℓ)).IsRoot x → x.im < 0 := by
      intro x hx
      rw [eulerProduct, Finset.prod_insert ha, ← eulerProduct, jensenRev_mul] at hx
      have := ffConv_root_im_lt (jensenRev_ne_zero hfa) (natDegree_jensenRev hfa)
        (jensenRev_ne_zero hF) (natDegree_jensenRev_le d _)
        (fun r hr => im_neg_of_isRoot_jensenRev_eulerFactor hqa hℓa hd hr) ihc hx
      simpa using this
    exact ⟨fun x hx => (hstrict x hx).le, fun _ => hstrict⟩

/-! ## Hermite–Biehler for polynomials -/

/-- The coefficientwise conjugate `P^#`. -/
def conjPoly (P : ℂ[X]) : ℂ[X] := P.map (starRingEnd ℂ)

theorem eval_conjPoly (P : ℂ[X]) (z : ℂ) : (conjPoly P).eval z = conj (P.eval (conj z)) := by
  rw [conjPoly, eval_map, ← Polynomial.eval₂_at_apply, Complex.conj_conj]

/-- For roots in the open lower half-plane and `Im z > 0`, `|P(z̄)| < |P(z)|`. -/
theorem norm_eval_conj_lt {P : ℂ[X]} (hP : P ≠ 0) (hdeg : 1 ≤ P.natDegree)
    (hroots : ∀ r, P.IsRoot r → r.im < 0) {z : ℂ} (hz : 0 < z.im) :
    ‖P.eval (conj z)‖ < ‖P.eval z‖ := by
  have hfac := (IsAlgClosed.splits P).eq_prod_roots
  have hev : ∀ w, P.eval w = P.leadingCoeff * (P.roots.map fun r => w - r).prod := by
    intro w
    conv_lhs => rw [hfac]
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    simp
  have hnorm : ∀ (w : ℂ) (s : Multiset ℂ),
      ‖(s.map fun r => w - r).prod‖ = (s.map fun r => ‖w - r‖).prod := by
    intro w s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih => simp [ih]
  rw [hev, hev, norm_mul, norm_mul, hnorm, hnorm]
  refine mul_lt_mul_of_pos_left ?_ (norm_pos_iff.2 (leadingCoeff_ne_zero.2 hP))
  have hne : P.roots ≠ 0 := by
    intro h0
    have := splits_iff_card_roots.1 (IsAlgClosed.splits P)
    rw [h0, Multiset.card_zero] at this
    omega
  have hlt : ∀ r ∈ P.roots, ‖conj z - r‖ < ‖z - r‖ := by
    intro r hr
    have hr' := hroots r ((mem_roots hP).1 hr)
    have key : ‖conj z - r‖ ^ 2 < ‖z - r‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]
      simp
      nlinarith
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 key
  have hpos : ∀ r ∈ P.roots, 0 < ‖z - r‖ := fun r hr =>
    lt_of_le_of_lt (norm_nonneg _) (hlt r hr)
  by_cases h0 : ∃ r ∈ P.roots, conj z - r = 0
  · obtain ⟨r, hr, hr0⟩ := h0
    have hzero : (P.roots.map fun r => ‖conj z - r‖).prod = 0 :=
      Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨r, hr, by rw [hr0, norm_zero]⟩)
    rw [hzero]
    exact Multiset.prod_pos fun x hx => by
      obtain ⟨r', hr', rfl⟩ := Multiset.mem_map.1 hx; exact hpos r' hr'
  · push Not at h0
    exact Multiset.prod_map_lt_prod_map hne _ _
      (fun r hr => norm_pos_iff.2 (h0 r hr)) hlt

/-- **Hermite–Biehler.** If all roots of `P` lie in the open lower half-plane (`deg P ≥ 1`), every
root of `P + P^#` is real. -/
theorem im_eq_zero_of_isRoot_add_conjPoly {P : ℂ[X]} (hP : P ≠ 0) (hdeg : 1 ≤ P.natDegree)
    (hroots : ∀ r, P.IsRoot r → r.im < 0) {z : ℂ} (hz : (P + conjPoly P).IsRoot z) : z.im = 0 := by
  have hval : P.eval z + conj (P.eval (conj z)) = 0 := by
    have := hz; rwa [IsRoot, eval_add, eval_conjPoly] at this
  rcases lt_trichotomy z.im 0 with hneg | h0 | hpos
  · exfalso
    have hc : 0 < (conj z).im := by simp; linarith
    have := norm_eval_conj_lt hP hdeg hroots hc
    rw [Complex.conj_conj] at this
    have h2 : ‖P.eval z‖ = ‖P.eval (conj z)‖ := by
      rw [eq_neg_of_add_eq_zero_left hval, norm_neg, Complex.norm_conj]
    linarith
  · exact h0
  · exfalso
    have := norm_eval_conj_lt hP hdeg hroots hpos
    have h2 : ‖P.eval z‖ = ‖P.eval (conj z)‖ := by
      rw [eq_neg_of_add_eq_zero_left hval, norm_neg, Complex.norm_conj]
    linarith

/-! ## Symmetrized finite Euler products are real-rooted at every degree -/

/-- **The finite free route on finite Euler products.** For every finite family of normalized Euler
factors (`‖q_i‖ < 1`, `ℓ_i > 0`) and every degree `d ≥ 1`, the functional-equation
symmetrization `R_d(G_S) + R_d(G_S)^#` of the reversed Jensen polynomial of the product has only
real roots. -/
theorem im_eq_zero_of_isRoot_symmetrized_eulerProduct {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (q : ι → ℂ) (ℓ : ι → ℝ) (hq : ∀ i ∈ S, ‖q i‖ < 1) (hℓ : ∀ i ∈ S, 0 < ℓ i)
    {d : ℕ} (hd : 1 ≤ d) {z : ℂ}
    (hz : (jensenRev d (eulerProduct S q ℓ) + conjPoly (jensenRev d (eulerProduct S q ℓ))).IsRoot z) :
    z.im = 0 := by
  have hc := constantCoeff_eulerProduct_ne_zero S q ℓ hq
  rcases S.eq_empty_or_nonempty with rfl | hS
  · rw [eulerProduct, Finset.prod_empty, jensenRev_one] at hz
    have hz' := hz
    simp [IsRoot, conjPoly] at hz'
    simp [hz'.1]
  · exact im_eq_zero_of_isRoot_add_conjPoly (jensenRev_ne_zero hc)
      (by rw [natDegree_jensenRev hc]; exact hd)
      ((roots_jensenRev_eulerProduct q ℓ hd S hq hℓ).2 hS) hz

/-- The prime instance: `q_p = p^{−σ}`, `ℓ_p = log p`, any `σ > 0`. -/
theorem im_eq_zero_of_isRoot_symmetrized_primeEulerProduct (S : Finset Nat.Primes) {σ : ℝ}
    (hσ : 0 < σ) {d : ℕ} (hd : 1 ≤ d) {z : ℂ}
    (hz : (jensenRev d (eulerProduct S (fun p => (((p : ℕ) : ℝ) ^ (-σ) : ℝ)) fun p => Real.log p) +
      conjPoly (jensenRev d (eulerProduct S (fun p => (((p : ℕ) : ℝ) ^ (-σ) : ℝ))
        fun p => Real.log p))).IsRoot z) : z.im = 0 := by
  refine im_eq_zero_of_isRoot_symmetrized_eulerProduct S _ _ (fun p _ => ?_) (fun p _ => ?_) hd hz
  · have h1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.one_lt
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg h1 (by linarith)
  · exact Real.log_pos (by exact_mod_cast p.prop.one_lt)

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.im_eq_zero_of_isRoot_symmetrized_primeEulerProduct
