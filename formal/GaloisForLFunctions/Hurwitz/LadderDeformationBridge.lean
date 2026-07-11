/-
# Hurwitz ladder deformation — the one-branch-point monodromy move

At the branch point `a = -n` (`n ≤ M`), in the coordinate `a = -n + e^z`, the deformed ladder
splits on the upper half-strip `0 < Im z < π` into

`dzeta c k (-n + e^z) = c_n·e^{-(s+k)z} + (factored tail + factored corrections)(e^z)`,

where the second summand is analytic on the half-plane `Re z < -log 2` and `2πi`-periodic,
while the singular exponential scales by `q = e^{-2πi s}` under `z ↦ z + 2πi` — the same
multiplier on every rung `k`.  Consequently any polynomial relation among the deformed rungs
with single-valued (polynomial-in-`a`) coefficients propagates from the deformation vector `c`
to the vector with `c_n` replaced by `q·c_n`: transport the relation to the model, extend it
from the upper half-strip to the full half-plane by the identity theorem, substitute
`z + 2πi`, and transport back — first to a punctured half-disc at `-n`, then to the whole
upper half-plane by the identity theorem again.

Iterating the move over all coordinates gives the relation on the whole multiplicative grid
`{(q^{m_0}, …, q^{m_M})}` — the input to the Vandermonde endgame.
-/
import GaloisForLFunctions.Hurwitz.LadderDeformation
import GaloisForLFunctions.Hurwitz.N2HZeta
import GaloisForLFunctions.Hurwitz.Encoding
import GaloisForLFunctions.Hurwitz.MonodromyScalar

open Complex HurwitzZetaShift HurwitzN2Tail HurwitzN2HZeta HurwitzSpine HurwitzOrbit

namespace HurwitzLadder

/-- Factored correction at branch point `n` from deformation coordinate `n' ≠ n` (zero at
`n' = n`): the cut-free form of `((n'-n) + x)^{-(s+k)}` near `x = 0`. -/
noncomputable def dcorr (s : ℂ) (k n n' : ℕ) (x : ℂ) : ℂ :=
  if n' = n then 0
  else ((n' : ℂ) - (n : ℂ)) ^ (-(s + (k : ℂ)))
    * (1 + x / ((n' : ℂ) - (n : ℂ))) ^ (-(s + (k : ℂ)))

theorem dcorr_exp_periodic (s : ℂ) (k n n' : ℕ) (z : ℂ) :
    dcorr s k n n' (Complex.exp (z + 2 * (Real.pi : ℂ) * Complex.I))
      = dcorr s k n n' (Complex.exp z) := by
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The deformed model at branch point `n`: deformed singular exponential, genuine factored
tail, and the finitely many factored corrections. -/
noncomputable def dmodel (s : ℂ) (M : ℕ) (c : Fin (M + 1) → ℂ) (n : Fin (M + 1)) (k : ℕ)
    (z : ℂ) : ℂ :=
  c n * Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s k (n : ℕ) (Complex.exp z)
    + ∑ n' : Fin (M + 1), (c n' - 1) * dcorr s k (n : ℕ) (n' : ℕ) (Complex.exp z)

/-- **The bridge**: on the upper half-strip `0 < Im z < π` the deformed ladder at
`a = -n + e^z` equals the model. -/
theorem dzeta_eq_dmodel {s : ℂ} (hs : 1 < s.re) {M : ℕ} (c : Fin (M + 1) → ℂ)
    (n : Fin (M + 1)) (k : ℕ) {z : ℂ} (h0 : 0 < z.im) (hπ : z.im < Real.pi) :
    dzeta s M c k (-((n : ℕ) : ℂ) + Complex.exp z) = dmodel s M c n k z := by
  have hxim : 0 < (Complex.exp z).im := by
    rw [Complex.exp_im]
    exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi h0 hπ)
  have hterm : ∀ n' : Fin (M + 1),
      (c n' - 1) * ((((n' : ℕ) : ℂ) + (-((n : ℕ) : ℂ) + Complex.exp z)) ^ (-(s + (k : ℂ))))
        = (if n' = n then (c n - 1) * Complex.exp (-(s + (k : ℂ)) * z) else 0)
          + (c n' - 1) * dcorr s k (n : ℕ) (n' : ℕ) (Complex.exp z) := by
    intro n'
    by_cases h : n' = n
    · subst h
      have hd : dcorr s k (n' : ℕ) (n' : ℕ) (Complex.exp z) = 0 := by
        rw [dcorr, if_pos rfl]
      rw [if_pos rfl, hd, mul_zero, add_zero]
      have hbase : (((n' : ℕ) : ℂ) + (-((n' : ℕ) : ℂ) + Complex.exp z)) = Complex.exp z := by
        ring
      rw [hbase, cexp_cpow_strip (by linarith [Real.pi_pos]) hπ.le]
    · have hne : (n' : ℕ) ≠ (n : ℕ) := fun hh => h (Fin.ext hh)
      rw [dcorr, if_neg hne, if_neg h, zero_add]
      have hbase : (((n' : ℕ) : ℂ) + (-((n : ℕ) : ℂ) + Complex.exp z))
          = (((n' : ℕ) : ℂ) - ((n : ℕ) : ℂ)) + Complex.exp z := by ring
      rw [hbase, term_split hxim hne]
  calc dzeta s M c k (-((n : ℕ) : ℂ) + Complex.exp z)
      = (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s k (n : ℕ) (Complex.exp z))
        + ∑ n' : Fin (M + 1),
            ((if n' = n then (c n - 1) * Complex.exp (-(s + (k : ℂ)) * z) else 0)
              + (c n' - 1) * dcorr s k (n : ℕ) (n' : ℕ) (Complex.exp z)) := by
        rw [dzeta, hzeta_eq_model hs k (n : ℕ) h0 hπ]
        congr 1
        exact Finset.sum_congr rfl (fun n' _ => hterm n')
    _ = dmodel s M c n k z := by
        rw [Finset.sum_add_distrib,
          Finset.sum_ite_eq' Finset.univ n
            (fun _ => (c n - 1) * Complex.exp (-(s + (k : ℂ)) * z)),
          if_pos (Finset.mem_univ n), dmodel]
        ring

/-- The model is differentiable on the half-plane `Re z < -log 2`. -/
theorem dmodel_differentiableOn {s : ℂ} (hs : 1 < s.re) {M : ℕ} (c : Fin (M + 1) → ℂ)
    (n : Fin (M + 1)) (k : ℕ) :
    DifferentiableOn ℂ (dmodel s M c n k) HurwitzN2BlockAnalytic.region := by
  apply DifferentiableOn.add
  apply DifferentiableOn.add
  · have : DifferentiableOn ℂ (fun z => Complex.exp (-(s + (k : ℂ)) * z))
        HurwitzN2BlockAnalytic.region := by fun_prop
    exact this.const_mul _
  · exact (tailFactored_analytic hs k (n : ℕ)).differentiableOn.comp
      Complex.differentiable_exp.differentiableOn HurwitzN2BlockAnalytic.exp_mapsTo
  · apply DifferentiableOn.fun_sum
    intro n' _
    apply DifferentiableOn.const_mul
    by_cases h : (n' : ℕ) = (n : ℕ)
    · refine DifferentiableOn.congr (differentiableOn_const 0) ?_
      intro z _
      simp [dcorr, h]
    · have hcst : DifferentiableOn ℂ
          (fun z : ℂ => (((n' : ℕ) : ℂ) - ((n : ℕ) : ℂ)) ^ (-(s + (k : ℂ)))
            * (1 + Complex.exp z / (((n' : ℕ) : ℂ) - ((n : ℕ) : ℂ))) ^ (-(s + (k : ℂ))))
          HurwitzN2BlockAnalytic.region := by
        apply DifferentiableOn.const_mul
        intro z hz
        apply DifferentiableAt.differentiableWithinAt
        have hxlt : ‖Complex.exp z‖ < 1 := by
          have h12 : ‖Complex.exp z‖ < 1 / 2 := HurwitzN2BlockAnalytic.exp_mapsTo hz
          linarith
        have hb : (1 + Complex.exp z / (((n' : ℕ) : ℂ) - ((n : ℕ) : ℂ)))
            ∈ Complex.slitPlane :=
          Complex.mem_slitPlane_iff.mpr (Or.inl (tailTerm_base_re_pos h hxlt))
        have haff : DifferentiableAt ℂ
            (fun y : ℂ => 1 + Complex.exp y / (((n' : ℕ) : ℂ) - ((n : ℕ) : ℂ))) z := by
          fun_prop
        exact ((hasStrictDerivAt_cpow_const hb).hasDerivAt.differentiableAt).comp z haff
      refine DifferentiableOn.congr hcst ?_
      intro z _
      rw [dcorr, if_neg h]

/-- **The shift move on the model.**  Substituting `z + 2πi` multiplies exactly the deformed
singular coefficient `c_n` by `q = e^{-2πi s}` and fixes every periodic part. -/
theorem dmodel_shift (s : ℂ) {M : ℕ} (c : Fin (M + 1) → ℂ) (n : Fin (M + 1)) (k : ℕ) (z : ℂ) :
    dmodel s M c n k (z + 2 * (Real.pi : ℂ) * Complex.I)
      = dmodel s M (Function.update c n (monoScalar s * c n)) n k z := by
  rw [dmodel, dmodel, HurwitzEncoding.Ek_shift, tailFactored_periodic]
  have hsum : (∑ n' : Fin (M + 1), (c n' - 1)
        * dcorr s k (n : ℕ) (n' : ℕ) (Complex.exp (z + 2 * (Real.pi : ℂ) * Complex.I)))
      = ∑ n' : Fin (M + 1), (Function.update c n (monoScalar s * c n) n' - 1)
        * dcorr s k (n : ℕ) (n' : ℕ) (Complex.exp z) := by
    refine Finset.sum_congr rfl (fun n' _ => ?_)
    rw [dcorr_exp_periodic]
    by_cases h : n' = n
    · subst h
      have hnn : (n' : ℕ) = (n' : ℕ) := rfl
      rw [dcorr, if_pos hnn, mul_zero, mul_zero]
    · rw [Function.update_of_ne h]
  rw [hsum, Function.update_self]
  have hq : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-s)) = monoScalar s := by
    rw [monoScalar]
    congr 1
    ring
  rw [hq]
  ring

section Relation

variable {N : ℕ}

/-- The deformed relation function on the `a`-domain: the polynomial `P` (coefficients in
`ℂ[a]`) evaluated on the deformed ladder. -/
noncomputable def relA (s : ℂ) (M : ℕ) (P : MvPolynomial (Fin (N + 1)) (Polynomial ℂ))
    (c : Fin (M + 1) → ℂ) (a : ℂ) : ℂ :=
  MvPolynomial.eval₂ (Polynomial.evalRingHom a)
    (fun k : Fin (N + 1) => dzeta s M c (k : ℕ) a) P

/-- The deformed relation function in the model coordinate at branch point `n`. -/
noncomputable def relZ (s : ℂ) (M : ℕ) (P : MvPolynomial (Fin (N + 1)) (Polynomial ℂ))
    (c : Fin (M + 1) → ℂ) (n : Fin (M + 1)) (z : ℂ) : ℂ :=
  MvPolynomial.eval₂ (Polynomial.evalRingHom (-((n : ℕ) : ℂ) + Complex.exp z))
    (fun k : Fin (N + 1) => dmodel s M c n (k : ℕ) z) P

theorem relA_eq_relZ {s : ℂ} (hs : 1 < s.re) {M : ℕ}
    (P : MvPolynomial (Fin (N + 1)) (Polynomial ℂ)) (c : Fin (M + 1) → ℂ)
    (n : Fin (M + 1)) {z : ℂ} (h0 : 0 < z.im) (hπ : z.im < Real.pi) :
    relA s M P c (-((n : ℕ) : ℂ) + Complex.exp z) = relZ s M P c n z := by
  have hg : (fun k : Fin (N + 1) => dzeta s M c (k : ℕ) (-((n : ℕ) : ℂ) + Complex.exp z))
      = fun k : Fin (N + 1) => dmodel s M c n (k : ℕ) z :=
    funext fun k => dzeta_eq_dmodel hs c n (k : ℕ) h0 hπ
  rw [relA, relZ, hg]

theorem relZ_shift {s : ℂ} {M : ℕ} (P : MvPolynomial (Fin (N + 1)) (Polynomial ℂ))
    (c : Fin (M + 1) → ℂ) (n : Fin (M + 1)) (z : ℂ) :
    relZ s M P c n (z + 2 * (Real.pi : ℂ) * Complex.I)
      = relZ s M P (Function.update c n (monoScalar s * c n)) n z := by
  have harg : -((n : ℕ) : ℂ) + Complex.exp (z + 2 * (Real.pi : ℂ) * Complex.I)
      = -((n : ℕ) : ℂ) + Complex.exp z := by
    rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hg : (fun k : Fin (N + 1) =>
        dmodel s M c n (k : ℕ) (z + 2 * (Real.pi : ℂ) * Complex.I))
      = fun k : Fin (N + 1) =>
        dmodel s M (Function.update c n (monoScalar s * c n)) n (k : ℕ) z :=
    funext fun k => dmodel_shift s c n (k : ℕ) z
  rw [relZ, relZ, harg, hg]

theorem relZ_differentiableOn {s : ℂ} (hs : 1 < s.re) {M : ℕ}
    (P : MvPolynomial (Fin (N + 1)) (Polynomial ℂ)) (c : Fin (M + 1) → ℂ) (n : Fin (M + 1)) :
    DifferentiableOn ℂ (relZ s M P c n) HurwitzN2BlockAnalytic.region := by
  have hexpand : relZ s M P c n = fun z =>
      ∑ d ∈ P.support, (MvPolynomial.coeff d P).eval (-((n : ℕ) : ℂ) + Complex.exp z)
        * ∏ i ∈ d.support, (dmodel s M c n (i : ℕ) z) ^ (d i) := by
    funext z
    rw [relZ, MvPolynomial.eval₂_eq]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Polynomial.coe_evalRingHom]
  rw [hexpand]
  apply DifferentiableOn.fun_sum
  intro d _
  apply DifferentiableOn.mul
  · have : DifferentiableOn ℂ
        (fun z => (MvPolynomial.coeff d P).eval (-((n : ℕ) : ℂ) + Complex.exp z))
        HurwitzN2BlockAnalytic.region := by fun_prop
    exact this
  · have hprod : DifferentiableOn ℂ
        (∏ i ∈ d.support, fun z => (dmodel s M c n (i : ℕ) z) ^ (d i))
        HurwitzN2BlockAnalytic.region := by
      apply DifferentiableOn.finsetProd
      intro i _
      exact (dmodel_differentiableOn hs c n (i : ℕ)).pow _
    refine DifferentiableOn.congr hprod ?_
    intro z _
    rw [Finset.prod_apply]

theorem relA_differentiableOn {s : ℂ} (hs : 1 < s.re) {M : ℕ}
    (P : MvPolynomial (Fin (N + 1)) (Polynomial ℂ)) (c : Fin (M + 1) → ℂ) :
    DifferentiableOn ℂ (relA s M P c) UHP := by
  have hexpand : relA s M P c = fun a =>
      ∑ d ∈ P.support, (MvPolynomial.coeff d P).eval a
        * ∏ i ∈ d.support, (dzeta s M c (i : ℕ) a) ^ (d i) := by
    funext a
    rw [relA, MvPolynomial.eval₂_eq]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Polynomial.coe_evalRingHom]
  rw [hexpand]
  apply DifferentiableOn.fun_sum
  intro d _
  apply DifferentiableOn.mul
  · exact (Polynomial.differentiable _).differentiableOn
  · have hprod : DifferentiableOn ℂ
        (∏ i ∈ d.support, fun a => (dzeta s M c (i : ℕ) a) ^ (d i)) UHP := by
      apply DifferentiableOn.finsetProd
      intro i _
      exact (dzeta_differentiableOn hs M c (i : ℕ)).pow _
    refine DifferentiableOn.congr hprod ?_
    intro a _
    rw [Finset.prod_apply]

/-- Extension of the model relation from the upper half-strip to the full half-plane
(identity theorem on the convex region `Re z < -log 2`). -/
theorem relZ_zero_of_upper {s : ℂ} (hs : 1 < s.re) {M : ℕ}
    (P : MvPolynomial (Fin (N + 1)) (Polynomial ℂ)) (c : Fin (M + 1) → ℂ) (n : Fin (M + 1))
    (hupper : ∀ z : ℂ, z ∈ HurwitzN2BlockAnalytic.region → 0 < z.im → z.im < Real.pi →
      relZ s M P c n z = 0) :
    ∀ z ∈ HurwitzN2BlockAnalytic.region, relZ s M P c n z = 0 := by
  have hFan : AnalyticOnNhd ℂ (relZ s M P c n) HurwitzN2BlockAnalytic.region :=
    (relZ_differentiableOn hs P c n).analyticOnNhd HurwitzN2BlockAnalytic.isOpen_region
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
  have hev : relZ s M P c n =ᶠ[nhds z₀] 0 :=
    Filter.eventuallyEq_of_mem (hWopen.mem_nhds hz₀W)
      (fun z hz => hupper z hz.1.1 hz.1.2 hz.2)
  have hzero : Set.EqOn (relZ s M P c n) 0 HurwitzN2BlockAnalytic.region :=
    hFan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hz₀mem hev
  intro z hz
  exact hzero hz

/-- **The one-point monodromy move on the `a`-domain relation.**  A vanishing deformed
relation propagates from `c` to the vector with `c_n` multiplied by `q = e^{-2πi s}`. -/
theorem relA_move {s : ℂ} (hs : 1 < s.re) {M : ℕ}
    (P : MvPolynomial (Fin (N + 1)) (Polynomial ℂ)) (c : Fin (M + 1) → ℂ) (n : Fin (M + 1))
    (h : ∀ a : ℂ, 0 < a.im → relA s M P c a = 0) :
    ∀ a : ℂ, 0 < a.im → relA s M P (Function.update c n (monoScalar s * c n)) a = 0 := by
  -- transport to the model on the upper half-strip
  have hupper : ∀ z : ℂ, z ∈ HurwitzN2BlockAnalytic.region → 0 < z.im → z.im < Real.pi →
      relZ s M P c n z = 0 := by
    intro z _ h0 hπ
    rw [← relA_eq_relZ hs P c n h0 hπ]
    apply h
    show 0 < (-((n : ℕ) : ℂ) + Complex.exp z).im
    have him : (-((n : ℕ) : ℂ) + Complex.exp z).im = (Complex.exp z).im := by simp
    rw [him, Complex.exp_im]
    exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi h0 hπ)
  -- extend to the full half-plane, shift, and read off the updated relation
  have hregion := relZ_zero_of_upper hs P c n hupper
  have hc' : ∀ z ∈ HurwitzN2BlockAnalytic.region,
      relZ s M P (Function.update c n (monoScalar s * c n)) n z = 0 := by
    intro z hz
    have hzshift : z + 2 * (Real.pi : ℂ) * Complex.I ∈ HurwitzN2BlockAnalytic.region := by
      show (z + 2 * (Real.pi : ℂ) * Complex.I).re < -Real.log 2
      have hre : (z + 2 * (Real.pi : ℂ) * Complex.I).re = z.re := by simp
      rw [hre]
      exact hz
    have h0 := hregion _ hzshift
    rwa [relZ_shift] at h0
  -- transport back to a punctured upper half-disc at `-n`
  have hpatch : ∀ a : ℂ, 0 < (a + ((n : ℕ) : ℂ)).im → ‖a + ((n : ℕ) : ℂ)‖ < 1 / 2 →
      relA s M P (Function.update c n (monoScalar s * c n)) a = 0 := by
    intro a him hnorm
    set x : ℂ := a + ((n : ℕ) : ℂ) with hx
    have hxne : x ≠ 0 := by
      intro hh
      rw [hh] at him
      simp at him
    set z : ℂ := Complex.log x with hz
    have hexpz : Complex.exp z = x := Complex.exp_log hxne
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hxne
    have hzre : z ∈ HurwitzN2BlockAnalytic.region := by
      show z.re < -Real.log 2
      rw [hz, Complex.log_re]
      have h1 : Real.log ‖x‖ < Real.log (1 / 2) := Real.log_lt_log hxpos hnorm
      have h2 : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
        rw [show (1 / 2 : ℝ) = 2⁻¹ from by norm_num, Real.log_inv]
      linarith
    have hsin : 0 < Real.sin x.arg := by
      rw [Complex.sin_arg]
      exact div_pos him hxpos
    have hargpos : 0 < x.arg := by
      rcases lt_trichotomy x.arg 0 with hlt | heq | hpos
      · have := Real.sin_neg_of_neg_of_neg_pi_lt hlt (Complex.neg_pi_lt_arg x)
        linarith
      · rw [heq, Real.sin_zero] at hsin
        exact absurd hsin (lt_irrefl 0)
      · exact hpos
    have hargpi : x.arg < Real.pi := by
      rcases lt_or_eq_of_le (Complex.arg_le_pi x) with hlt | heq
      · exact hlt
      · rw [heq, Real.sin_pi] at hsin
        exact absurd hsin (lt_irrefl 0)
    have h0z : 0 < z.im := by rw [hz, Complex.log_im]; exact hargpos
    have hπz : z.im < Real.pi := by rw [hz, Complex.log_im]; exact hargpi
    have ha_eq : a = -((n : ℕ) : ℂ) + Complex.exp z := by
      rw [hexpz, hx]
      ring
    rw [ha_eq, relA_eq_relZ hs P _ n h0z hπz]
    exact hc' z hzre
  -- identity theorem on the upper half-plane
  have hAn : AnalyticOnNhd ℂ (relA s M P (Function.update c n (monoScalar s * c n))) UHP :=
    (relA_differentiableOn hs P _).analyticOnNhd isOpen_UHP
  set a₀ : ℂ := -((n : ℕ) : ℂ) + ((1 / 4 : ℝ) : ℂ) * Complex.I with ha₀
  have ha₀x : a₀ + ((n : ℕ) : ℂ) = ((1 / 4 : ℝ) : ℂ) * Complex.I := by rw [ha₀]; ring
  have ha₀mem : a₀ ∈ UHP := by
    show 0 < a₀.im
    have : a₀.im = (a₀ + ((n : ℕ) : ℂ)).im := by simp
    rw [this, ha₀x]
    simp
  have hOopen : IsOpen {a : ℂ | 0 < (a + ((n : ℕ) : ℂ)).im ∧ ‖a + ((n : ℕ) : ℂ)‖ < 1 / 2} := by
    apply IsOpen.inter
    · have hcont : Continuous fun a : ℂ => (a + ((n : ℕ) : ℂ)).im :=
        Complex.continuous_im.comp (continuous_id.add continuous_const)
      exact isOpen_lt continuous_const hcont
    · have hcont : Continuous fun a : ℂ => ‖a + ((n : ℕ) : ℂ)‖ :=
        (continuous_id.add continuous_const).norm
      exact isOpen_lt hcont continuous_const
  have ha₀O : a₀ ∈ {a : ℂ | 0 < (a + ((n : ℕ) : ℂ)).im ∧ ‖a + ((n : ℕ) : ℂ)‖ < 1 / 2} := by
    constructor
    · rw [ha₀x]
      simp
    · rw [ha₀x, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
      rw [Real.norm_eq_abs]
      norm_num
  have hev : relA s M P (Function.update c n (monoScalar s * c n)) =ᶠ[nhds a₀] 0 :=
    Filter.eventuallyEq_of_mem (hOopen.mem_nhds ha₀O) (fun a ha => hpatch a ha.1 ha.2)
  have hzero := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_UHP
    ha₀mem hev
  intro a ha
  exact hzero ha

/-- **Grid invariance.**  Iterating the one-point move: a vanishing relation for the genuine
ladder holds for every deformation vector `(q^{m_0}, …, q^{m_M})`. -/
theorem relA_grid {s : ℂ} (hs : 1 < s.re) {M : ℕ}
    (P : MvPolynomial (Fin (N + 1)) (Polynomial ℂ))
    (h1 : ∀ a : ℂ, 0 < a.im → relA s M P (fun _ => 1) a = 0) :
    ∀ m : Fin (M + 1) → ℕ, ∀ a : ℂ, 0 < a.im →
      relA s M P (fun n => monoScalar s ^ m n) a = 0 := by
  suffices H : ∀ K : ℕ, ∀ m : Fin (M + 1) → ℕ, (∑ n, m n) = K → ∀ a : ℂ, 0 < a.im →
      relA s M P (fun n => monoScalar s ^ m n) a = 0 by
    exact fun m => H (∑ n, m n) m rfl
  intro K
  induction K using Nat.strong_induction_on with
  | _ K ih =>
    intro m hm a ha
    by_cases h0 : ∀ n, m n = 0
    · have hc : (fun n : Fin (M + 1) => monoScalar s ^ m n) = fun _ => 1 := by
        funext n
        rw [h0 n, pow_zero]
      rw [hc]
      exact h1 a ha
    · obtain ⟨n₀, hn₀⟩ := not_forall.mp h0
      have hn₀pos : 1 ≤ m n₀ := Nat.one_le_iff_ne_zero.mpr hn₀
      set m' : Fin (M + 1) → ℕ := Function.update m n₀ (m n₀ - 1) with hm'
      have hsum' : (∑ n, m' n) = K - 1 := by
        rw [hm', Finset.sum_update_of_mem (Finset.mem_univ n₀)]
        have hK : m n₀ + ∑ n ∈ Finset.univ \ {n₀}, m n = K := by
          rw [← Finset.erase_eq, Finset.add_sum_erase Finset.univ m (Finset.mem_univ n₀)]
          exact hm
        omega
      have hKpos : 1 ≤ K := by
        rw [← hm]
        calc 1 ≤ m n₀ := hn₀pos
          _ ≤ ∑ n, m n := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ n₀)
      have hprev : ∀ a : ℂ, 0 < a.im → relA s M P (fun n => monoScalar s ^ m' n) a = 0 :=
        fun a' ha' => ih (K - 1) (by omega) m' hsum' a' ha'
      have hstep := relA_move hs P (fun n => monoScalar s ^ m' n) n₀ hprev
      have hupd : Function.update (fun n => monoScalar s ^ m' n) n₀
          (monoScalar s * monoScalar s ^ m' n₀) = fun n => monoScalar s ^ m n := by
        funext n
        by_cases h : n = n₀
        · subst h
          rw [Function.update_self, hm', Function.update_self]
          rw [show monoScalar s * monoScalar s ^ (m n - 1) = monoScalar s ^ (m n - 1 + 1) from
            by rw [pow_succ]; ring]
          congr 1
          omega
        · rw [Function.update_of_ne h, hm', Function.update_of_ne h]
      rw [← hupd]
      exact hstep a ha

end Relation

end HurwitzLadder
