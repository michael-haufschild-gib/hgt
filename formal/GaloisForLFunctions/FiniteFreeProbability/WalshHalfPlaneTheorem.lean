import GaloisForLFunctions.FiniteFreeProbability.AdditiveConvolution
import GaloisForLFunctions.HTGeometry.RealRootedCoefficientLimit

/-!
# Walsh's theorem for the finite free additive convolution

If all roots of `p` lie in the closed half-plane `Im ≤ a` and all roots of `q` in `Im ≤ b`, then all
roots of `p ⊞_d q` lie in `Im ≤ a + b` (`deg p = d`, `deg q ≤ d`). In particular the finite free
convolution of two real-rooted real polynomials is real-rooted.

Mechanism. At a point `z` with `Im z > a + b`, `(p ⊞_d q)(z)` is the apolarity pairing of
`f = p(z + ·)`, whose roots lie in `Im ≤ c := a − Im z`, with `q`. Peeling the roots `μ` of `q` one
at a time replaces `f` by polar derivatives with poles `−μ`, each strictly above the line `Im = c`.
Laguerre's theorem keeps the roots of every polar derivative in `Im ≤ c` and lowers the degree by
exactly one; the last pairing is a nonzero multiple of a leading coefficient.

Laguerre's theorem is an averaging statement: at a root `x` above the line, `Σ_r 1/(x − r)` equals
`m/(x − ζ)`, but inversion maps `{Im u ≥ h}` into a closed disc that the pole's image `1/(x − ζ)`
lies strictly outside of, and discs are convex.
-/

open Polynomial Complex

namespace FiniteFreeProbability

noncomputable section

/-- `‖2h + i u‖² = ‖u‖² + 4h(h − Im u)`. -/
theorem norm_sq_two_mul_add_I_mul (h : ℝ) (u : ℂ) :
    ‖(2 * h : ℂ) + I * u‖ ^ 2 = ‖u‖ ^ 2 + 4 * h * (h - u.im) := by
  rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]
  simp
  ring

/-- Inversion followed by the shift by `i/(2h)`: `1/u + i/(2h) = (2h + i u)/(2h u)`. -/
theorem inv_sub_center_eq {h : ℝ} (hh : h ≠ 0) {u : ℂ} (hu : u ≠ 0) :
    u⁻¹ - (-(I / (2 * h))) = ((2 * h : ℂ) + I * u) / ((2 * h : ℂ) * u) := by
  have : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  field_simp
  ring

/-- Inversion maps `{Im u ≥ h}` (`h > 0`) into the closed disc of centre `−i/(2h)`, radius
`1/(2h)`. -/
theorem norm_inv_sub_center_le {h : ℝ} (hh : 0 < h) {u : ℂ} (hu : h ≤ u.im) :
    ‖u⁻¹ - (-(I / (2 * h)))‖ ≤ 1 / (2 * h) := by
  have hu0 : u ≠ 0 := fun h0 => by rw [h0] at hu; simp at hu; linarith
  have hn : 0 < ‖u‖ := norm_pos_iff.2 hu0
  have hle : ‖(2 * h : ℂ) + I * u‖ ≤ ‖u‖ := by
    have h1 := norm_sq_two_mul_add_I_mul h u
    have h2 : 4 * h * (h - u.im) ≤ 0 := by nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by linarith)
  have h2h : ‖(2 * h : ℂ)‖ = 2 * h := by
    rw [show (2 * h : ℂ) = ((2 * h : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  rw [inv_sub_center_eq hh.ne' hu0, norm_div, norm_mul, h2h,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- A nonzero point strictly below `Im = h` is inverted strictly outside that disc. -/
theorem lt_norm_inv_sub_center {h : ℝ} (hh : 0 < h) {u : ℂ} (hu0 : u ≠ 0) (hu : u.im < h) :
    1 / (2 * h) < ‖u⁻¹ - (-(I / (2 * h)))‖ := by
  have hn : 0 < ‖u‖ := norm_pos_iff.2 hu0
  have hlt : ‖u‖ < ‖(2 * h : ℂ) + I * u‖ := by
    have h1 := norm_sq_two_mul_add_I_mul h u
    have h2 : 0 < 4 * h * (h - u.im) := by nlinarith
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by linarith)
  have h2h : ‖(2 * h : ℂ)‖ = 2 * h := by
    rw [show (2 * h : ℂ) = ((2 * h : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  rw [inv_sub_center_eq hh.ne' hu0, norm_div, norm_mul, h2h,
    div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **Averaging law.** If every `u` in a nonempty multiset has `Im u ≥ h > 0`, then
`Σ 1/u = card · (1/u₀)` forces `Im u₀ ≥ h` for `u₀ ≠ 0`. -/
theorem le_im_of_sum_inv_eq {s : Multiset ℂ} {h : ℝ} (hh : 0 < h) (hs : s ≠ 0)
    (hu : ∀ u ∈ s, h ≤ u.im) {u₀ : ℂ} (hu₀ : u₀ ≠ 0)
    (hsum : (s.map fun u => u⁻¹).sum = (Multiset.card s : ℂ) * u₀⁻¹) : h ≤ u₀.im := by
  by_contra hlt
  push Not at hlt
  set c₀ : ℂ := -(I / (2 * h))
  have hcard : 0 < Multiset.card s := Multiset.card_pos.2 hs
  have hshift : ((s.map fun u => u⁻¹ - c₀)).sum = (Multiset.card s : ℂ) * (u₀⁻¹ - c₀) := by
    rw [Multiset.sum_map_sub, hsum, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul]
    ring
  have hupper : ‖((s.map fun u => u⁻¹ - c₀)).sum‖ ≤ (Multiset.card s : ℝ) * (1 / (2 * h)) := by
    refine (norm_multiset_sum_le _).trans ?_
    rw [Multiset.map_map]
    have := Multiset.sum_le_card_nsmul (s.map ((fun x => ‖x‖) ∘ fun u => u⁻¹ - c₀)) (1 / (2 * h))
      (by
        intro x hx
        obtain ⟨u, hus, rfl⟩ := Multiset.mem_map.1 hx
        exact norm_inv_sub_center_le hh (hu u hus))
    simpa [nsmul_eq_mul] using this
  rw [hshift, norm_mul, Complex.norm_natCast] at hupper
  have hlow := lt_norm_inv_sub_center hh hu₀ hlt
  have hc : (0 : ℝ) < Multiset.card s := by exact_mod_cast hcard
  nlinarith

/-- The imaginary part of a multiset sum. -/
theorem im_multiset_sum (s : Multiset ℂ) : s.sum.im = (s.map Complex.im).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]

/-- **Laguerre's theorem, half-plane form.** Let `g` have degree exactly `m ≥ 1` and all roots in
`Im ≤ c`, and let the pole `ζ` lie strictly above, `Im ζ > c`. Then the polar derivative
`m g − (X − ζ) g'` is nonzero of degree exactly `m − 1` with all roots in `Im ≤ c`. -/
theorem polarDeriv_laguerre {g : ℂ[X]} {m : ℕ} {c : ℝ} {ζ : ℂ} (hm : 1 ≤ m)
    (hdeg : g.natDegree = m) (hroots : ∀ r, g.IsRoot r → r.im ≤ c) (hζ : c < ζ.im) :
    polarDeriv m ζ g ≠ 0 ∧ (polarDeriv m ζ g).natDegree = m - 1 ∧
      ∀ x, (polarDeriv m ζ g).IsRoot x → x.im ≤ c := by
  have hg0 : g ≠ 0 := by rintro rfl; simp at hdeg; omega
  have hsplit : g.Splits := IsAlgClosed.splits g
  have hcardm : Multiset.card g.roots = m := by
    rw [← hdeg]; exact (splits_iff_card_roots.1 hsplit)
  have hrootsim : ∀ r ∈ g.roots, r.im ≤ c := fun r hr => hroots r ((mem_roots hg0).1 hr)
  -- the coefficient of `X^{m-1}` is `lc · (m ζ − Σ roots)`, with positive imaginary part
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hcoeff : (polarDeriv (k + 1) ζ g).coeff k =
      g.leadingCoeff * (((k : ℂ) + 1) * ζ - g.roots.sum) := by
    rw [coeff_polarDeriv]
    have hnext : g.coeff k = -g.leadingCoeff * g.roots.sum := by
      have h := hsplit.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
      rwa [nextCoeff_of_natDegree_pos (by omega), hdeg, Nat.add_sub_cancel] at h
    have hlead : g.coeff (k + 1) = g.leadingCoeff := by rw [leadingCoeff, hdeg]
    rw [hnext, hlead]; push_cast; ring
  have hsumim : g.roots.sum.im ≤ ((k : ℝ) + 1) * c := by
    rw [im_multiset_sum]
    have := Multiset.sum_le_card_nsmul (g.roots.map Complex.im) c
      (by intro x hx; obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx; exact hrootsim r hr)
    simpa [hcardm, nsmul_eq_mul] using this
  have hne : g.leadingCoeff * (((k : ℂ) + 1) * ζ - g.roots.sum) ≠ 0 := by
    refine mul_ne_zero (leadingCoeff_ne_zero.2 hg0) fun h0 => ?_
    have him := congrArg Complex.im h0
    simp only [sub_im, mul_im, add_re, natCast_re, one_re, add_im, natCast_im, one_im,
      zero_im] at him
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    nlinarith
  have hcoeff_ne : (polarDeriv (k + 1) ζ g).coeff k ≠ 0 := hcoeff ▸ hne
  have hP0 : polarDeriv (k + 1) ζ g ≠ 0 := fun h0 => hcoeff_ne (by rw [h0, coeff_zero])
  have hdegP : (polarDeriv (k + 1) ζ g).natDegree = k := by
    refine natDegree_eq_of_le_of_coeff_ne_zero ?_ hcoeff_ne
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    have hN' : k < N := by exact_mod_cast hN
    rw [coeff_polarDeriv, coeff_eq_zero_of_natDegree_lt (show g.natDegree < N + 1 by omega)]
    rcases Nat.lt_or_ge (k + 1) N with h | h
    · rw [coeff_eq_zero_of_natDegree_lt (show g.natDegree < N by omega)]; ring
    · have : N = k + 1 := by omega
      subst this; push_cast; ring
  refine ⟨hP0, by simpa using hdegP, fun x hx => ?_⟩
  -- root location
  by_contra hxc
  push Not at hxc
  have hgx : g.eval x ≠ 0 := fun h0 => by linarith [hroots x h0]
  have hval : ((k + 1 : ℕ) : ℂ) * g.eval x = (x - ζ) * (derivative g).eval x := by
    have := hx
    rw [IsRoot, polarDeriv, eval_sub, eval_mul, eval_mul, eval_C, eval_sub, eval_X, eval_C] at this
    exact sub_eq_zero.1 this
  have hxζ : x - ζ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hval
    exact hgx ((mul_eq_zero.1 hval).resolve_left (by exact_mod_cast Nat.succ_ne_zero k))
  have hlog := hsplit.eval_derivative_div_eval_of_ne_zero hgx
  have hsum : ((g.roots.map fun r => x - r).map fun u => u⁻¹).sum =
      (Multiset.card (g.roots.map fun r => x - r) : ℂ) * (x - ζ)⁻¹ := by
    rw [Multiset.map_map, Multiset.card_map, hcardm]
    have h1 : (g.roots.map ((fun u : ℂ => u⁻¹) ∘ fun r => x - r)).sum =
        (derivative g).eval x / g.eval x := by
      rw [hlog]; congr 1; refine Multiset.map_congr rfl fun r _ => ?_; simp
    rw [h1, div_eq_iff hgx]
    field_simp
    linear_combination (-1 : ℂ) * hval
  have hcardpos : g.roots.map (fun r => x - r) ≠ 0 := by
    intro h0
    have := congrArg Multiset.card h0
    rw [Multiset.card_map, hcardm] at this
    simp at this
  have hlow := le_im_of_sum_inv_eq (h := x.im - c) (by linarith) hcardpos
    (by
      intro u hu
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hu
      simp only [sub_im]
      linarith [hrootsim r hr])
    hxζ hsum
  simp only [sub_im] at hlow
  linarith

/-- **Iterated peeling.** For `g` of degree exactly `d` with roots in `Im ≤ c` and poles `−μ` strictly
above (`Im μ < −c`), the pairing of `g` with `a · Π (X − μ)` is nonzero. -/
theorem apolarPairing_ne_zero {c : ℝ} :
    ∀ (s : Multiset ℂ) (d : ℕ) (g : ℂ[X]) (a : ℂ), a ≠ 0 → Multiset.card s ≤ d → g ≠ 0 →
      g.natDegree = d → (∀ r, g.IsRoot r → r.im ≤ c) → (∀ μ ∈ s, μ.im < -c) →
      apolarPairing d g (C a * (s.map fun μ => X - C μ).prod) ≠ 0 := by
  intro s
  induction s using Multiset.induction_on with
  | empty =>
    intro d g a ha _ hg hdeg _ _
    rw [Multiset.map_zero, Multiset.prod_zero, mul_one, apolarPairing_C]
    refine mul_ne_zero (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero d) ?_) ha
    rw [← hdeg]; exact leadingCoeff_ne_zero.2 hg
  | cons μ t ih =>
    intro d g a ha hcard hg hdeg hroots hμ
    rw [Multiset.card_cons] at hcard
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have hq : C a * ((μ ::ₘ t).map fun μ => X - C μ).prod =
        (X - C μ) * (C a * (t.map fun μ => X - C μ).prod) := by
      rw [Multiset.map_cons, Multiset.prod_cons]; ring
    have hqdeg : (C a * (t.map fun μ => X - C μ).prod).natDegree ≤ d' := by
      rw [natDegree_C_mul ha, natDegree_multiset_prod_X_sub_C_eq_card]; omega
    rw [hq, apolarPairing_X_sub_C_mul _ _ _ _ hqdeg]
    have hζ : c < (-μ).im := by
      have := hμ μ (Multiset.mem_cons_self μ t); simp only [neg_im]; linarith
    obtain ⟨hP0, hPdeg, hProots⟩ := polarDeriv_laguerre (by omega) hdeg hroots hζ
    exact ih d' _ a ha (by omega) hP0 (by simpa using hPdeg) hProots
      (fun ν hν => hμ ν (Multiset.mem_cons_of_mem hν))

/-- **Walsh's theorem, half-plane form.** For `deg p = d`, `deg q ≤ d`, `p, q ≠ 0`, roots of `p` in
`Im ≤ a` and roots of `q` in `Im ≤ b`, `p ⊞_d q` has no zero with `Im z > a + b`. -/
theorem eval_ffConv_ne_zero {d : ℕ} {p q : ℂ[X]} (hp0 : p ≠ 0) (hp : p.natDegree = d)
    (hq0 : q ≠ 0) (hq : q.natDegree ≤ d) {a b : ℝ} (hpa : ∀ r, p.IsRoot r → r.im ≤ a)
    (hqb : ∀ μ, q.IsRoot μ → μ.im ≤ b) {z : ℂ} (hz : a + b < z.im) :
    (ffConv d p q).eval z ≠ 0 := by
  rw [eval_ffConv]
  refine div_ne_zero ?_ (by exact_mod_cast Nat.factorial_ne_zero d)
  have hqfac := (IsAlgClosed.splits q).eq_prod_roots
  have htay0 : taylor z p ≠ 0 := fun h0 => hp0 (by
    have := congrArg (taylor (-z)) h0
    rwa [taylor_taylor, neg_add_cancel, taylor_zero, map_zero] at this)
  rw [hqfac]
  refine apolarPairing_ne_zero (c := a - z.im) _ d _ _ (leadingCoeff_ne_zero.2 hq0) ?_ htay0
    (by rw [natDegree_taylor, hp]) ?_ ?_
  · rw [splits_iff_card_roots.1 (IsAlgClosed.splits q)]; exact hq
  · intro r hr
    have : p.IsRoot (r + z) := by rw [IsRoot, ← taylor_eval]; exact hr
    have := hpa _ this
    simp only [add_im] at this
    linarith
  · intro μ hμ
    have := hqb μ ((mem_roots hq0).1 hμ)
    linarith

/-- Root location form of Walsh's theorem. -/
theorem ffConv_root_im_le {d : ℕ} {p q : ℂ[X]} (hp0 : p ≠ 0) (hp : p.natDegree = d)
    (hq0 : q ≠ 0) (hq : q.natDegree ≤ d) {a b : ℝ} (hpa : ∀ r, p.IsRoot r → r.im ≤ a)
    (hqb : ∀ μ, q.IsRoot μ → μ.im ≤ b) {z : ℂ} (hz : (ffConv d p q).IsRoot z) :
    z.im ≤ a + b := by
  by_contra h
  exact eval_ffConv_ne_zero hp0 hp hq0 hq hpa hqb (lt_of_not_ge h) hz

/-- **Walsh's theorem.** The finite free convolution of two real-rooted real polynomials
(`deg p = d`, `deg q ≤ d`, `q ≠ 0`) is real-rooted. -/
theorem splits_ffConv {d : ℕ} {p q : ℝ[X]} (hp : p.Splits) (hq : q.Splits) (hp0 : p ≠ 0)
    (hpd : p.natDegree = d) (hq0 : q ≠ 0) (hqd : q.natDegree ≤ d) : (ffConv d p q).Splits := by
  set φ := algebraMap ℝ ℂ
  have hinj : Function.Injective φ := φ.injective
  have hreal : ∀ {P : ℝ[X]}, P.Splits → P ≠ 0 → ∀ r, (P.map φ).IsRoot r → r.im ≤ 0 := by
    intro P hP hP0 r hr
    have : (aeval r P : ℂ) = 0 := by rwa [aeval_def, eval₂_eq_eval_map]
    exact (GaloisForLFunctions.HTGeometry.im_eq_zero_of_splits hP hP0 this).le
  have hp0' : p.map φ ≠ 0 := (Polynomial.map_ne_zero_iff hinj).2 hp0
  have hq0' : q.map φ ≠ 0 := (Polynomial.map_ne_zero_iff hinj).2 hq0
  have hle : ∀ r : ℂ, (aeval r (ffConv d p q) : ℂ) = 0 → r.im ≤ 0 := by
    intro r hr
    have hr' : (ffConv d (p.map φ) (q.map φ)).IsRoot r := by
      rw [IsRoot, ← ffConv_map, ← eval₂_eq_eval_map, ← aeval_def]; exact hr
    simpa using ffConv_root_im_le hp0' (by rw [natDegree_map_eq_of_injective hinj, hpd]) hq0'
      (by rw [natDegree_map_eq_of_injective hinj]; exact hqd) (hreal hp hp0) (hreal hq hq0) hr'
  refine GaloisForLFunctions.HTGeometry.splits_of_forall_complex_root_real d _
    (natDegree_ffConv_le d p q hpd.le) fun r hr => ?_
  have hconj : (aeval (starRingEnd ℂ r) (ffConv d p q) : ℂ) = 0 := by
    have h := Polynomial.aeval_algHom_apply Complex.conjAe r (ffConv d p q)
    simpa [hr] using h
  have h1 := hle r hr
  have h2 := hle _ hconj
  simp only [conj_im] at h2
  linarith

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.splits_ffConv
#print axioms FiniteFreeProbability.ffConv_root_im_le
