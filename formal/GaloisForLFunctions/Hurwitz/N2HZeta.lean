/-
# Hurwitz N=2 / all-N — the genuine `hzeta` capstones

The proven model capstones (`HurwitzN2HalfInteger.hurwitz_n2_unconditional_all_noninteger`,
`HurwitzAllNHalfInteger.allN_quad_vanish_genuine_all_noninteger`) state the relation hypothesis
against the analytic MODEL blocks `exp(-(s+k)z) + tailFactored s k n (e^z)`.  This file closes the
remaining bridge to the actual Hurwitz zeta function `hzeta s a = ∑' m, (m+a)^{-s}`:

* `term_split` — the principal-branch product split `((m-n)+x)^c = (m-n)^c · (1+x/(m-n))^c` for
  `0 < Im x`.  This is the branch-cut analysis: for `m < n` the base `(m-n)+x` sits just above the
  negative real axis and `arg(m-n) + arg(1+x/(m-n)) = π + (negative) ∈ (-π, π]` exactly because
  `Im(x/(m-n)) < 0`; for `m > n` the arg sum is a single arg.  On the LOWER half-plane the split
  fails for `m < n` (the arg sum leaves the principal window), so the upper-half hypothesis in the
  capstones below is the honest one — and it suffices, because the model relation then extends from
  the upper half-strip to the full strip by the identity theorem.
* `principal_tail_eq_tailFactored`, `hzeta_eq_model` — for `x = e^z` with `0 < Im z < π`:
  `hzeta (s+k) (-n+e^z) = e^{-(s+k)z} + tailFactored s k n (e^z)`.
* `model_relation_of_hzeta_relation` — a genuine `hzeta` relation at `a = -n + x` (`‖x‖ < 1/2`,
  `0 < Im x`) forces the model relation on the full strip (identity theorem on the half-plane).
* `hurwitz_n2_hzeta_unconditional` / `hurwitz_n2_hzeta_upper_half_plane` — the genuine N=2
  statements: a polynomial-coefficient quadratic relation among the actual `hzeta (s+k) ·` (`k ≤ 2`)
  near the negative-integer ray (upper side) has only the zero coefficients (`Re s > 1`, `s ∉ ℤ`).
* `hurwitz_allN_hzeta_quadratic_block` — the same bridge feeding the all-`N` quadratic-block
  theorem: the full quadratic filtration `AqN q w` vanishes for `w ≤ 2N`.
-/
import GaloisForLFunctions.Hurwitz.N2HalfInteger
import GaloisForLFunctions.Hurwitz.N2BlockAnalytic
import GaloisForLFunctions.Hurwitz.AllNHalfInteger
import Mathlib.Analysis.Complex.Convex

open Complex HurwitzN2Tail HurwitzZetaShift HurwitzSpine

namespace HurwitzN2HZeta

/-- **Principal-branch product split, upper half-plane.** For `m ≠ n` and `0 < Im x`,
`((m-n)+x)^c = (m-n)^c · (1+x/(m-n))^c` with principal `cpow` throughout. -/
theorem term_split {c x : ℂ} (hxim : 0 < x.im) {m n : ℕ} (hmn : m ≠ n) :
    (((m : ℂ) - (n : ℂ)) + x) ^ c
      = ((m : ℂ) - (n : ℂ)) ^ c * (1 + x / ((m : ℂ) - (n : ℂ))) ^ c := by
  set r : ℝ := (m : ℝ) - (n : ℝ) with hr
  have hrne : r ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn)
  have hμ : ((m : ℂ) - (n : ℂ)) = (r : ℂ) := by rw [hr]; push_cast; ring
  have hμne : ((r : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hrne
  set w : ℂ := 1 + x / (r : ℂ) with hw
  have hwim : w.im = x.im * r⁻¹ := by
    have hdiv : x / (r : ℂ) = x * ((r⁻¹ : ℝ) : ℂ) := by push_cast; ring
    rw [hw, Complex.add_im, hdiv, Complex.mul_im]
    simp
  have hwimne : w.im ≠ 0 := by
    rw [hwim]; exact mul_ne_zero (ne_of_gt hxim) (inv_ne_zero hrne)
  have hwne : w ≠ 0 := fun h => hwimne (by simp [h])
  have hfactor : (r : ℂ) + x = (r : ℂ) * w := by
    rw [hw]; field_simp
  have harg : (r : ℂ).arg + w.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    rcases lt_or_gt_of_ne hrne with hneg | hpos
    · have h1 : (r : ℂ).arg = Real.pi :=
        Complex.arg_eq_pi_iff.mpr ⟨by simpa using hneg, by simp⟩
      have h2 : w.arg < 0 := Complex.arg_neg_iff.mpr (by
        rw [hwim]
        exact mul_neg_of_pos_of_neg hxim (inv_lt_zero.mpr hneg))
      have h3 := Complex.neg_pi_lt_arg w
      constructor
      · rw [h1]; linarith [Real.pi_pos]
      · rw [h1]; linarith
    · have h1 : (r : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg hpos.le
      rw [h1, zero_add]
      exact ⟨Complex.neg_pi_lt_arg w, Complex.arg_le_pi w⟩
  have hlog : Complex.log ((r : ℂ) * w) = Complex.log (r : ℂ) + Complex.log w :=
    (Complex.log_mul_eq_add_log_iff hμne hwne).mpr harg
  calc (((m : ℂ) - (n : ℂ)) + x) ^ c
      = ((r : ℂ) * w) ^ c := by rw [hμ, hfactor]
    _ = Complex.exp ((Complex.log (r : ℂ) + Complex.log w) * c) := by
        rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hμne hwne), hlog]
    _ = Complex.exp (Complex.log (r : ℂ) * c) * Complex.exp (Complex.log w * c) := by
        rw [add_mul, Complex.exp_add]
    _ = (r : ℂ) ^ c * w ^ c := by
        rw [← Complex.cpow_def_of_ne_zero hμne, ← Complex.cpow_def_of_ne_zero hwne]
    _ = ((m : ℂ) - (n : ℂ)) ^ c * (1 + x / ((m : ℂ) - (n : ℂ))) ^ c := by
        rw [hw, ← hμ]

/-- **The principal Hurwitz tail IS the factored analytic tail on the upper half-plane.** Term-wise
application of `term_split`; no summability input is needed (`tsum_congr`). -/
theorem principal_tail_eq_tailFactored (s : ℂ) (k n : ℕ) {x : ℂ} (hxim : 0 < x.im) :
    (∑' m : ℕ, (if m = n then 0 else ((m : ℂ) + (-(n : ℂ) + x)) ^ (-(s + (k : ℂ)))))
      = tailFactored s k n x := by
  rw [tailFactored]
  refine tsum_congr fun m => ?_
  by_cases h : m = n
  · simp [h]
  · simp only [if_neg h]
    have hbase : (m : ℂ) + (-(n : ℂ) + x) = ((m : ℂ) - (n : ℂ)) + x := by ring
    rw [hbase, term_split hxim h]

/-- **The genuine Hurwitz zeta equals the model block on the upper half-strip.** For `0 < Im z < π`,
`hzeta (s+k) (-n+e^z) = e^{-(s+k)z} + tailFactored s k n (e^z)`. -/
theorem hzeta_eq_model {s : ℂ} (hs1 : 1 < s.re) (k n : ℕ) {z : ℂ}
    (h0 : 0 < z.im) (hπ : z.im < Real.pi) :
    hzeta (s + (k : ℂ)) (-(n : ℂ) + Complex.exp z)
      = Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s k n (Complex.exp z) := by
  have hxim : 0 < (Complex.exp z).im := by
    rw [Complex.exp_im]
    exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi h0 hπ)
  rw [hzeta_local_split_shift hs1 k n (Complex.exp z),
    principal_tail_eq_tailFactored s k n hxim,
    cexp_cpow_strip (by linarith [Real.pi_pos]) hπ.le]

end HurwitzN2HZeta

namespace HurwitzN2HZeta

/-- **hzeta relation ⟹ model relation on the full strip.** If the genuine `hzeta` relation holds at
`a = -n + x` for all `‖x‖ < 1/2` with `0 < Im x`, then the model relation (the exact `hrel` input of
the N=2 and all-`N` model capstones) holds for ALL `z` in the strip `Re z < -log 2`,
`-π < Im z < π`: on the upper half-strip it is the `hzeta_eq_model` transport, and the model
expression is analytic on the half-plane (entire pieces + `tailFactored_analytic ∘ exp`), so the
identity theorem extends the vanishing across the full (convex, hence preconnected) half-plane. -/
theorem model_relation_of_hzeta_relation {s : ℂ} (hs1 : 1 < s.re) {K : ℕ}
    (q : Fin K → Fin K → Polynomial ℂ) (l : Fin K → Polynomial ℂ) (cc : Polynomial ℂ) (n : ℕ)
    (hrel : ∀ x : ℂ, ‖x‖ < 1 / 2 → 0 < x.im →
      (∑ i : Fin K, ∑ j : Fin K, (q i j).eval (-(n : ℂ) + x)
          * (hzeta (s + (i : ℂ)) (-(n : ℂ) + x) * hzeta (s + (j : ℂ)) (-(n : ℂ) + x)))
        + (∑ k : Fin K, (l k).eval (-(n : ℂ) + x) * hzeta (s + (k : ℂ)) (-(n : ℂ) + x))
        + cc.eval (-(n : ℂ) + x) = 0) :
    ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im → z.im < Real.pi →
      (∑ i : Fin K, ∑ j : Fin K, (q i j).eval (-(n : ℂ) + Complex.exp z)
          * ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin K, (l k).eval (-(n : ℂ) + Complex.exp z)
            * (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0 := by
  set F : ℂ → ℂ := fun z =>
    (∑ i : Fin K, ∑ j : Fin K, (q i j).eval (-(n : ℂ) + Complex.exp z)
        * ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
          * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
      + (∑ k : Fin K, (l k).eval (-(n : ℂ) + Complex.exp z)
          * (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
      + cc.eval (-(n : ℂ) + Complex.exp z) with hF
  -- the model function vanishes on the upper half-strip: transport of the hzeta relation
  have hupper : ∀ z : ℂ, z.re < -Real.log 2 → 0 < z.im → z.im < Real.pi → F z = 0 := by
    intro z hz h0 hπ
    have hnorm : ‖Complex.exp z‖ < 1 / 2 := HurwitzN2BlockAnalytic.exp_mapsTo hz
    have hxim : 0 < (Complex.exp z).im := by
      rw [Complex.exp_im]
      exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi h0 hπ)
    have hbr : ∀ kk : ℕ, hzeta (s + (kk : ℂ)) (-(n : ℂ) + Complex.exp z)
        = Complex.exp (-(s + (kk : ℂ)) * z) + tailFactored s kk n (Complex.exp z) :=
      fun kk => hzeta_eq_model hs1 kk n h0 hπ
    have hr := hrel (Complex.exp z) hnorm hxim
    simp only [hbr] at hr
    simpa [hF] using hr
  -- the model function is analytic on the half-plane
  have hFan : AnalyticOnNhd ℂ F HurwitzN2BlockAnalytic.region := by
    rw [hF]
    apply DifferentiableOn.analyticOnNhd _ HurwitzN2BlockAnalytic.isOpen_region
    have htail : ∀ kk : ℕ,
        DifferentiableOn ℂ (fun z => tailFactored s kk n (Complex.exp z))
          HurwitzN2BlockAnalytic.region :=
      fun kk => (tailFactored_analytic hs1 kk n).differentiableOn.comp
        Complex.differentiable_exp.differentiableOn HurwitzN2BlockAnalytic.exp_mapsTo
    have hpoly : ∀ p : Polynomial ℂ,
        DifferentiableOn ℂ (fun z => p.eval (-(n : ℂ) + Complex.exp z))
          HurwitzN2BlockAnalytic.region := by
      intro p; fun_prop
    have hexp : ∀ c : ℂ,
        DifferentiableOn ℂ (fun z => Complex.exp (c * z))
          HurwitzN2BlockAnalytic.region := by
      intro c; fun_prop
    exact ((DifferentiableOn.fun_sum fun i _ => DifferentiableOn.fun_sum fun j _ =>
        (hpoly _).mul (((hexp _).add (htail _)).mul ((hexp _).add (htail _)))).add
      (DifferentiableOn.fun_sum fun k _ => (hpoly _).mul ((hexp _).add (htail _)))).add
      (hpoly cc)
  -- identity theorem on the convex half-plane
  have hpre : IsPreconnected HurwitzN2BlockAnalytic.region :=
    (convex_halfSpace_re_lt (-Real.log 2)).isPreconnected
  set z₀ : ℂ := ⟨-Real.log 2 - 1, Real.pi / 2⟩ with hz₀def
  have hz₀mem : z₀ ∈ HurwitzN2BlockAnalytic.region := by
    show z₀.re < -Real.log 2
    rw [hz₀def]
    norm_num
  have hWopen : IsOpen (HurwitzN2BlockAnalytic.region
      ∩ {z : ℂ | 0 < z.im} ∩ {z : ℂ | z.im < Real.pi}) :=
    (HurwitzN2BlockAnalytic.isOpen_region.inter
      (isOpen_lt continuous_const Complex.continuous_im)).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hz₀W : z₀ ∈ HurwitzN2BlockAnalytic.region
      ∩ {z : ℂ | 0 < z.im} ∩ {z : ℂ | z.im < Real.pi} := by
    refine ⟨⟨hz₀mem, ?_⟩, ?_⟩
    · show (0 : ℝ) < z₀.im
      rw [hz₀def]
      simpa using Real.pi_pos
    · show z₀.im < Real.pi
      rw [hz₀def]
      show Real.pi / 2 < Real.pi
      linarith [Real.pi_pos]
  have hev : F =ᶠ[nhds z₀] 0 :=
    Filter.eventuallyEq_of_mem (hWopen.mem_nhds hz₀W)
      (fun z hz => hupper z hz.1.1 hz.1.2 hz.2)
  have hzero : Set.EqOn F 0 HurwitzN2BlockAnalytic.region :=
    hFan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hz₀mem hev
  intro z hz _h1 _h2
  simpa [hF] using hzero hz

end HurwitzN2HZeta

namespace HurwitzN2HZeta

/-- **Hurwitz N=2 — no quadratic relation among the ACTUAL `ζ(s,a), ζ(s+1,a), ζ(s+2,a)`,
unconditional.** With `Re s > 1` and `s ∉ ℤ` only: if the genuine polynomial-coefficient quadratic
relation among `hzeta (s+k) a` (`k ≤ 2`) holds at every `a = -n + x` with `n ≥ N`, `‖x‖ < 1/2`,
`0 < Im x`, then the symmetric quadratic form, the linear coefficients, and the constant all
vanish.  This is the genuine-`hzeta` form of
`HurwitzN2HalfInteger.hurwitz_n2_unconditional_all_noninteger`. -/
theorem hurwitz_n2_hzeta_unconditional {s : ℂ} (hs1 : 1 < s.re)
    (hsZ : ∀ k : ℤ, (k : ℂ) ≠ s)
    (q : Fin 3 → Fin 3 → Polynomial ℂ) (l : Fin 3 → Polynomial ℂ) (cc : Polynomial ℂ) {N : ℕ}
    (hrel : ∀ n, N ≤ n → ∀ x : ℂ, ‖x‖ < 1 / 2 → 0 < x.im →
      (∑ i : Fin 3, ∑ j : Fin 3, (q i j).eval (-(n : ℂ) + x)
          * (hzeta (s + (i : ℂ)) (-(n : ℂ) + x) * hzeta (s + (j : ℂ)) (-(n : ℂ) + x)))
        + (∑ k : Fin 3, (l k).eval (-(n : ℂ) + x) * hzeta (s + (k : ℂ)) (-(n : ℂ) + x))
        + cc.eval (-(n : ℂ) + x) = 0) :
    q 0 0 = 0 ∧ q 2 2 = 0 ∧ q 1 1 = 0 ∧ q 0 2 + q 2 0 = 0
      ∧ l 2 = 0 ∧ l 0 = 0 ∧ l 1 = 0 ∧ cc = 0 := by
  refine HurwitzN2HalfInteger.hurwitz_n2_unconditional_all_noninteger hs1 hsZ q l cc (N := N) ?_
  intro n hn
  exact model_relation_of_hzeta_relation hs1 q l cc n (hrel n hn)

/-- **Hurwitz N=2, upper-half-plane form.** If the genuine quadratic `hzeta` relation holds at every
`a` with `Im a > 0`, all coefficients vanish. -/
theorem hurwitz_n2_hzeta_upper_half_plane {s : ℂ} (hs1 : 1 < s.re)
    (hsZ : ∀ k : ℤ, (k : ℂ) ≠ s)
    (q : Fin 3 → Fin 3 → Polynomial ℂ) (l : Fin 3 → Polynomial ℂ) (cc : Polynomial ℂ)
    (hrel : ∀ a : ℂ, 0 < a.im →
      (∑ i : Fin 3, ∑ j : Fin 3, (q i j).eval a
          * (hzeta (s + (i : ℂ)) a * hzeta (s + (j : ℂ)) a))
        + (∑ k : Fin 3, (l k).eval a * hzeta (s + (k : ℂ)) a) + cc.eval a = 0) :
    q 0 0 = 0 ∧ q 2 2 = 0 ∧ q 1 1 = 0 ∧ q 0 2 + q 2 0 = 0
      ∧ l 2 = 0 ∧ l 0 = 0 ∧ l 1 = 0 ∧ cc = 0 :=
  hurwitz_n2_hzeta_unconditional hs1 hsZ q l cc (N := 0)
    (fun n _ x _ hxim => hrel (-(n : ℂ) + x) (by simpa using hxim))

/-- **All-`N` quadratic block against the ACTUAL Hurwitz zeta.** A genuine polynomial-coefficient
quadratic relation among `hzeta (s+k) ·` (`0 ≤ k ≤ N`) near the negative-integer ray (upper side)
kills the entire quadratic filtration: `AqN q w = 0` for all `w ≤ 2N` (`Re s > 1`, `s ∉ ℤ` only). -/
theorem hurwitz_allN_hzeta_quadratic_block (Nb : ℕ) {s : ℂ} (hs1 : 1 < s.re)
    (hsZ : ∀ k : ℤ, (k : ℂ) ≠ s)
    (q : Fin (Nb + 1) → Fin (Nb + 1) → Polynomial ℂ) (l : Fin (Nb + 1) → Polynomial ℂ)
    (cc : Polynomial ℂ) {M : ℕ}
    (hrel : ∀ n, M ≤ n → ∀ x : ℂ, ‖x‖ < 1 / 2 → 0 < x.im →
      (∑ i : Fin (Nb + 1), ∑ j : Fin (Nb + 1), (q i j).eval (-(n : ℂ) + x)
          * (hzeta (s + (i : ℂ)) (-(n : ℂ) + x) * hzeta (s + (j : ℂ)) (-(n : ℂ) + x)))
        + (∑ k : Fin (Nb + 1), (l k).eval (-(n : ℂ) + x) * hzeta (s + (k : ℂ)) (-(n : ℂ) + x))
        + cc.eval (-(n : ℂ) + x) = 0) :
    ∀ w, w ≤ 2 * Nb → HurwitzAllNQuadFilt.AqN q w = 0 := by
  refine HurwitzAllNHalfInteger.allN_quad_vanish_genuine_all_noninteger
    (N := Nb) (s := s) (M := M) hs1 hsZ q l cc ?_
  intro n hn
  exact model_relation_of_hzeta_relation hs1 q l cc n (hrel n hn)

end HurwitzN2HZeta
