import GaloisForLFunctions.RHTower.ZetaZeroAntiCrystalLaw
import GaloisForLFunctions.HTGeometry.PolyaClassPhaseRigidity

/-!
# The gapless realization law for Ξ

**Theorem** (`not_exists_lowerPolyaClass_realization`). For no `h > 0` is there a lower Pólya
function `G`, i.e. a locally uniform limit of polynomials with all roots in `Im ≤ 0`, such that

  `Ξ(t) = Re G(t + ih)` for all real `t`.

Equivalently, no Hermite–Biehler realization `E(z) = G(z + ih)` of `Ξ = Re E` has a resonance-free
strip `−h < Im z ≤ 0`. Every lossless realization of Ξ must have resonances arbitrarily close to
the real axis. The cosine case `G` real (`cos(hD)` preimages) is CANNOT-497. Here `G` is
arbitrary.

**Proof.**
* *RH.* The polynomials `P_m(z) = (p_m(z + ih) + p̄_m(z − ih))/2` converge to Ξ. They have only
  real zeros because `|p_m(z + ih)| > |p_m(z̄ + ih)|` for `Im z > 0` factor by factor
  (`norm_eval_ne_of_im_ne_zero`). Hurwitz transfer gives RH
  (`riemannHypothesis_of_XiC_locally_uniform_real_zero_approximants`).
* *Phase.* `G` has no zero above the real axis, so `Ξ(t) = A(t) cos φ(t)` with `A > 0`,
  `φ' = −ω` and `ω(s) ≤ e^{2|s−t|/h} ω(t)` (`exists_phase_rep`,
  `LowerPolyaClass.phaseSpeed_le_exp_mul`).
* *Rigidity.* Consecutive zeros enclose phase `π`, so the zeros are simple and the ordered
  ordinates are `(h/2)`-rigid (`gap_rigidity_of_phase`). This contradicts the anti-crystal law
  (`not_rigidOrdinates`).
-/

open Complex Filter Topology Set Polynomial
open GaloisForLFunctions.HTGeometry (LowerPolyaClass phaseSpeed exists_phase_rep
  gap_rigidity_of_phase)

namespace RHTower

noncomputable section

/-- Two entire functions that agree on the real line agree everywhere. -/
theorem eq_of_eq_on_real {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfg : ∀ t : ℝ, f t = g t) : f = g := by
  have hfa : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
  have hga : AnalyticOnNhd ℂ g univ := fun z _ => hg.analyticAt z
  have hseq : Tendsto (fun n : ℕ => (((1 : ℝ) / (n + 1) : ℝ) : ℂ)) atTop (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rw [← Complex.ofReal_zero]
      exact (Complex.continuous_ofReal.tendsto 0).comp this
    · simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero]
      positivity
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = g z :=
    hseq.frequently (Frequently.of_forall fun n => hfg _)
  funext z
  exact hfa.eqOn_of_preconnected_of_frequently_eq hga isPreconnected_univ (mem_univ 0) hfreq
    (mem_univ z)

/-- Conjugating the coefficients: `(p̄)(w) = conj (p(w̄))`. -/
theorem eval_map_conj (p : ℂ[X]) (w : ℂ) :
    (p.map (starRingEnd ℂ)).eval w = (starRingEnd ℂ) (p.eval ((starRingEnd ℂ) w)) := by
  rw [Polynomial.eval_map, Polynomial.eval, Polynomial.hom_eval₂, RingHom.comp_id,
    Complex.conj_conj]

/-- A strict product comparison for nonnegative factors over a nonempty multiset. -/
theorem multiset_prod_map_lt {s : Multiset ℂ} (hs : s ≠ 0) {f g : ℂ → ℝ}
    (hf : ∀ r ∈ s, 0 ≤ f r) (hfg : ∀ r ∈ s, f r < g r) :
    (s.map f).prod < (s.map g).prod := by
  induction s using Multiset.induction_on with
  | empty => exact absurd rfl hs
  | cons a t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    have ha := hf a (Multiset.mem_cons_self a t)
    have hga := hfg a (Multiset.mem_cons_self a t)
    by_cases ht : t = 0
    · subst ht; simpa using hga
    have hf' : ∀ r ∈ t, 0 ≤ f r := fun r hr => hf r (Multiset.mem_cons_of_mem hr)
    have hfg' : ∀ r ∈ t, f r < g r := fun r hr => hfg r (Multiset.mem_cons_of_mem hr)
    have hP : 0 ≤ (t.map f).prod := Multiset.prod_nonneg fun x hx => by
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx; exact hf' r hr
    exact mul_lt_mul'' hga (ih ht hf' hfg') ha hP

/-- `‖Π f(r)‖ = Π ‖f(r)‖` over a multiset. -/
theorem norm_multiset_prod_map (s : Multiset ℂ) (f : ℂ → ℂ) :
    ‖(s.map f).prod‖ = (s.map fun r => ‖f r‖).prod := by
  have := map_multiset_prod (normHom : ℂ →*₀ ℝ) (s.map f)
  simpa [Multiset.map_map] using this

/-- The factor identity `‖z + ih − r‖² − ‖z̄ + ih − r‖² = 4 Im z (h − Im r)`. -/
theorem norm_sq_sub_norm_sq_conj (z r : ℂ) (h : ℝ) :
    ‖z + h * I - r‖ ^ 2 - ‖(starRingEnd ℂ) z + h * I - r‖ ^ 2 = 4 * z.im * (h - r.im) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.add_im,
    Complex.conj_im, Complex.mul_im]
  ring

/-- **Strict Hermite–Biehler for lower polynomials.** If `p` has roots in `Im ≤ 0`, `h > 0`,
`Im z ≠ 0` and `‖p(z + ih)‖ = ‖p(z̄ + ih)‖`, then `p` has no roots. -/
theorem roots_eq_zero_of_norm_eval_eq {p : ℂ[X]} (hroots : ∀ r ∈ p.roots, r.im ≤ 0) {h : ℝ}
    (hh : 0 < h) {z : ℂ} (hz : z.im ≠ 0)
    (heq : ‖p.eval (z + h * I)‖ = ‖p.eval ((starRingEnd ℂ) z + h * I)‖) : p.roots = 0 := by
  by_contra hne
  have hp : p ≠ 0 := fun h0 => hne (by rw [h0, Polynomial.roots_zero])
  have hlead : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  rw [(IsAlgClosed.splits p).eval_eq_prod_roots, (IsAlgClosed.splits p).eval_eq_prod_roots,
    norm_mul, norm_mul, norm_multiset_prod_map, norm_multiset_prod_map] at heq
  have hln : 0 < ‖p.leadingCoeff‖ := norm_pos_iff.mpr hlead
  have hpos : ∀ r ∈ p.roots, 0 < h - r.im := fun r hr => by linarith [hroots r hr]
  rcases lt_or_gt_of_ne hz with hneg | hposz
  · have hlt := multiset_prod_map_lt hne (f := fun r => ‖z + h * I - r‖)
      (g := fun r => ‖(starRingEnd ℂ) z + h * I - r‖) (fun r _ => norm_nonneg _)
      (fun r hr => by
        have h1 := norm_sq_sub_norm_sq_conj z r h
        have h3 : ‖z + h * I - r‖ ^ 2 < ‖(starRingEnd ℂ) z + h * I - r‖ ^ 2 := by
          have := hpos r hr; nlinarith
        exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h3)
    have := mul_lt_mul_of_pos_left hlt hln
    linarith
  · have hlt := multiset_prod_map_lt hne (f := fun r => ‖(starRingEnd ℂ) z + h * I - r‖)
      (g := fun r => ‖z + h * I - r‖) (fun r _ => norm_nonneg _)
      (fun r hr => by
        have h1 := norm_sq_sub_norm_sq_conj z r h
        have h3 : ‖(starRingEnd ℂ) z + h * I - r‖ ^ 2 < ‖z + h * I - r‖ ^ 2 := by
          have := hpos r hr; nlinarith
        exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h3)
    have := mul_lt_mul_of_pos_left hlt hln
    linarith

theorem uniformContinuous_half : UniformContinuous (fun w : ℂ => w / 2) := by
  refine Metric.uniformContinuous_iff.mpr fun ε hε => ⟨ε, hε, fun {a b} hab => ?_⟩
  rw [dist_eq_norm] at hab ⊢
  rw [← sub_div, norm_div]
  simp only [Complex.norm_ofNat]
  linarith [norm_nonneg (a - b)]

/-- **RH from a lower Pólya realization.** If `Ξ(t) = Re G(t + ih)` on `ℝ` for a lower Pólya
function `G` and `h > 0`, then RH holds. -/
theorem riemannHypothesis_of_lowerPolyaClass_realization {h : ℝ} (hh : 0 < h) {G : ℂ → ℂ}
    (hG : LowerPolyaClass G) (hrep : ∀ t : ℝ, Xi t = (G ((t : ℂ) + h * I)).re) :
    RiemannHypothesis := by
  have hGd := hG.differentiable
  obtain ⟨p, hroots, hconv⟩ := hG
  set P : ℕ → ℂ → ℂ := fun m z =>
    ((p m).eval (z + h * I) + ((p m).map (starRingEnd ℂ)).eval (z - h * I)) / 2 with hP
  set Gs : ℂ → ℂ := fun z =>
    (G (z + h * I) + (starRingEnd ℂ) (G ((starRingEnd ℂ) z + h * I))) / 2 with hGs
  have hPconj : ∀ m z, ((p m).map (starRingEnd ℂ)).eval (z - h * I) =
      (starRingEnd ℂ) ((p m).eval ((starRingEnd ℂ) z + h * I)) := by
    intro m z
    rw [eval_map_conj]
    congr 2
    simp [map_sub, Complex.conj_ofReal]
  -- convergence `P → Gs`
  have hA : TendstoLocallyUniformly (fun m z => (p m).eval (z + h * I)) (fun z => G (z + h * I))
      atTop := hconv.comp (fun z => z + h * I) (by fun_prop)
  have hB : TendstoLocallyUniformly (fun m z => (starRingEnd ℂ) ((p m).eval ((starRingEnd ℂ) z + h * I)))
      (fun z => (starRingEnd ℂ) (G ((starRingEnd ℂ) z + h * I))) atTop := by
    have h1 := hconv.comp (fun z => (starRingEnd ℂ) z + h * I)
      (by have := Complex.continuous_conj; fun_prop)
    exact Complex.isometry_conj.uniformContinuous.comp_tendstoLocallyUniformly h1
  have hconvP : TendstoLocallyUniformly P Gs atTop := by
    have h2 := uniformContinuous_half.comp_tendstoLocallyUniformly (hA.add hB)
    have e : (fun m => (fun w : ℂ => w / 2) ∘ ((fun m z => (p m).eval (z + h * I)) +
        fun m z => (starRingEnd ℂ) ((p m).eval ((starRingEnd ℂ) z + h * I))) m) = P := by
      funext m z
      simp only [hP, Function.comp_apply, Pi.add_apply, hPconj]
    rw [e] at h2
    exact h2
  have hPd : ∀ m, Differentiable ℂ (P m) := by
    intro m
    simp only [hP]
    have h1 : Differentiable ℂ (fun z => (p m).eval (z + h * I)) :=
      (Polynomial.differentiable (p m)).comp (differentiable_id.add_const _)
    have h2 : Differentiable ℂ (fun z => ((p m).map (starRingEnd ℂ)).eval (z - h * I)) := by
      have hs : Differentiable ℂ (fun z : ℂ => z - (h : ℂ) * I) :=
        differentiable_id.sub (differentiable_const _)
      exact (Polynomial.differentiable ((p m).map (starRingEnd ℂ))).comp hs
    exact (h1.add h2).div_const 2
  -- `Gs = XiC`
  have hGsd : Differentiable ℂ Gs := by
    have := (tendstoLocallyUniformlyOn_univ.mpr hconvP).differentiableOn
      (Eventually.of_forall fun m => (hPd m).differentiableOn) isOpen_univ
    exact differentiableOn_univ.mp this
  have hXiCd : Differentiable ℂ XiC := fun z =>
    (xi_differentiable.comp ((differentiable_const _).add
      (differentiable_id.mul (differentiable_const _)))) z
  have hGsXi : Gs = XiC := by
    refine eq_of_eq_on_real hGsd hXiCd fun t => ?_
    rw [XiC_ofReal, hrep t]
    simp only [hGs, Complex.conj_ofReal]
    rw [Complex.add_conj]
    push_cast
    ring
  rw [hGsXi] at hconvP
  refine riemannHypothesis_of_XiC_locally_uniform_real_zero_approximants hconvP
    (Eventually.of_forall hPd) ?_
  -- eventually `P_m(0) ≠ 0`, and then all zeros of `P_m` are real
  have hX0 : XiC 0 ≠ 0 := by
    rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp, XiC_ofReal]
    exact_mod_cast Xi_zero_pos.ne'
  have hev0 : ∀ᶠ m in atTop, P m 0 ≠ 0 :=
    ((tendstoLocallyUniformlyOn_univ.mpr hconvP).tendsto_at (mem_univ 0)).eventually_ne hX0
  filter_upwards [hev0] with m hm0
  intro z hz
  by_contra hzim
  have hsum : (p m).eval (z + h * I) = -((starRingEnd ℂ) ((p m).eval ((starRingEnd ℂ) z + h * I))) := by
    have : P m z = 0 := hz
    simp only [hP, hPconj] at this
    linear_combination (2 : ℂ) * this
  have hnorm : ‖(p m).eval (z + h * I)‖ = ‖(p m).eval ((starRingEnd ℂ) z + h * I)‖ := by
    rw [hsum, norm_neg, Complex.norm_conj]
  have hr := roots_eq_zero_of_norm_eval_eq (hroots m) hh hzim hnorm
  have hdeg : (p m).natDegree = 0 := by
    rw [(IsAlgClosed.splits (p m)).natDegree_eq_card_roots, hr, Multiset.card_zero]
  have hC := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hconst : ∀ w, P m w = ((p m).coeff 0 + (starRingEnd ℂ) ((p m).coeff 0)) / 2 := by
    intro w
    simp only [hP]
    rw [hC]
    simp [Polynomial.eval_C, Polynomial.map_C]
  apply hm0
  rw [hconst 0, ← hconst z]
  exact hz


/-- A lower Pólya function with `G(a) ≠ 0` has no zero above the real axis. -/
theorem lowerPolyaClass_im_nonpos_of_eq_zero {G : ℂ → ℂ} (hG : LowerPolyaClass G) {a : ℂ}
    (ha : G a ≠ 0) {z : ℂ} (hz : G z = 0) : z.im ≤ 0 := by
  have hGd := hG.differentiable
  obtain ⟨p, hroots, hconv⟩ := hG
  have hev : ∀ᶠ m in atTop, (p m).eval a ≠ 0 :=
    ((tendstoLocallyUniformlyOn_univ.mpr hconv).tendsto_at (mem_univ a)).eventually_ne ha
  have := zero_mem_closed_of_tendstoLocallyUniformly (S := {w : ℂ | w.im ≤ 0}) hconv
    (fun w _ => hGd.analyticAt w) (Eventually.of_forall fun m => Polynomial.differentiable (p m))
    (isClosed_le Complex.continuous_im continuous_const)
    (by
      filter_upwards [hev] with m hm
      intro w hw
      have hp : p m ≠ 0 := fun h0 => hm (by rw [h0, Polynomial.eval_zero])
      exact hroots m w ((Polynomial.mem_roots hp).mpr hw))
    ha hz
  exact this

/-- The derivative of `Ξ` along `ℝ` from a realization `Ξ(t) = Re G(t + ih)`. -/
theorem hasDerivAt_Xi_of_realization {G : ℂ → ℂ} (hGd : Differentiable ℂ G) {h : ℝ}
    (hrep : ∀ t : ℝ, Xi t = (G ((t : ℂ) + h * I)).re) (y : ℝ) :
    HasDerivAt Xi (deriv G ((y : ℂ) + h * I)).re y := by
  have hE : HasDerivAt (fun t : ℝ => G ((t : ℂ) + h * I)) (deriv G ((y : ℂ) + h * I)) y := by
    have h1 : HasDerivAt (fun z : ℂ => G (z + h * I)) (deriv G ((y : ℂ) + h * I)) (y : ℂ) :=
      ((hGd ((y : ℂ) + h * I)).hasDerivAt).comp_add_const (y : ℂ) (h * I)
    exact h1.comp_ofReal
  have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y hE
  have hfun : Xi = fun t : ℝ => (G ((t : ℂ) + h * I)).re := funext hrep
  rw [hfun]
  exact this

/-- The derivative of `Ξ` along `ℝ` through `ξ`. -/
theorem hasDerivAt_Xi_xi (y : ℝ) :
    HasDerivAt Xi (deriv xi ((1 / 2 : ℂ) + y * I) * I).re y := by
  have hp : HasDerivAt (fun t : ℝ => (1 / 2 : ℂ) + t * I) I y := by
    simpa using ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (1 / 2 : ℂ)
  have hx := (xi_differentiable _).hasDerivAt.comp y hp
  have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y hx
  exact this

/-- **Simple real zeros.** At a real zero of a realization with positive phase speed, the
derivative of `Ξ` is nonzero. -/
theorem re_deriv_ne_zero_of_realization {G : ℂ → ℂ} {h : ℝ} {y : ℝ}
    (hne : G ((y : ℂ) + h * I) ≠ 0) (hω : 0 < phaseSpeed G h y)
    (hzero : (G ((y : ℂ) + h * I)).re = 0) : (deriv G ((y : ℂ) + h * I)).re ≠ 0 := by
  set E := G ((y : ℂ) + h * I) with hE
  set q := deriv G ((y : ℂ) + h * I) / E with hq
  have hd : deriv G ((y : ℂ) + h * I) = E * q := by rw [hq]; field_simp
  have hEim : E.im ≠ 0 := by
    intro h0; apply hne; exact Complex.ext hzero h0
  have hqim : q.im = -phaseSpeed G h y := by simp [GaloisForLFunctions.HTGeometry.phaseSpeed, hq, hE]
  rw [hd, Complex.mul_re, hzero, zero_mul, zero_sub, hqim]
  intro h0
  have : E.im * phaseSpeed G h y = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · exact hEim h1
  · linarith

/-- Two distinct zero copies with the same complex point force a multiple zero, hence a critical
point of `ξ`. -/
theorem deriv_xi_eq_zero_of_copies {q₁ q₂ : XiZeroCopy} (hne : q₁ ≠ q₂)
    (heq : (q₁.1 : ℂ) = (q₂.1 : ℂ)) : deriv xi (q₁.1 : ℂ) = 0 := by
  have hρ : q₁.1 = q₂.1 := Subtype.ext heq
  set ρ := q₁.1 with hρdef
  set e := xiZeroCopyFiberEquiv ρ with he
  have hdist : e.symm ⟨q₁, rfl⟩ ≠ e.symm ⟨q₂, hρ.symm⟩ := by
    intro h; apply hne
    have := congrArg Subtype.val (e.symm.injective h)
    exact this
  have hcard : 2 ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)).toNat := by
    by_contra hlt
    push Not at hlt
    apply hdist
    have : ∀ a b : Fin ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)).toNat, a = b := by
      intro a b; ext; omega
    exact this _ _
  have hmult : 2 ≤ xiSupportMultiplicity ρ := hcard
  rw [xiSupportMultiplicity_eq_analyticOrderAt_toNat] at hmult
  have horder : (2 : ℕ∞) ≤ analyticOrderAt xi (ρ : ℂ) := by
    rcases eq_or_ne (analyticOrderAt xi (ρ : ℂ)) ⊤ with htop | htop
    · rw [htop]; exact le_top
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
      rw [← hn] at hmult ⊢
      simp only [ENat.toNat_coe] at hmult
      exact_mod_cast hmult
  -- a zero of order at least two is a critical point
  have hf : AnalyticAt ℂ xi (ρ : ℂ) := xi_differentiable.analyticAt _
  rcases eq_or_ne (analyticOrderAt xi (ρ : ℂ)) ⊤ with htop | htop
  · have hev : xi =ᶠ[𝓝 (ρ : ℂ)] fun _ => (0 : ℂ) := analyticOrderAt_eq_top.mp htop
    rw [hev.deriv_eq]; simp
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    obtain ⟨g, hg, -, hev⟩ := hf.analyticOrderAt_eq_natCast.mp hn.symm
    have hn2 : 2 ≤ n := by rw [← hn] at horder; exact_mod_cast horder
    have hev' : xi =ᶠ[𝓝 (ρ : ℂ)] fun w => (w - (ρ : ℂ)) ^ n * g w := hev.mono fun w hw => by
      rw [hw, smul_eq_mul]
    rw [hev'.deriv_eq]
    have hp : HasDerivAt (fun w : ℂ => (w - (ρ : ℂ)) ^ n)
        ((n : ℂ) * ((ρ : ℂ) - (ρ : ℂ)) ^ (n - 1) * 1) (ρ : ℂ) :=
      ((hasDerivAt_id (ρ : ℂ)).sub_const (ρ : ℂ)).pow n
    have hd : HasDerivAt (fun w : ℂ => (w - (ρ : ℂ)) ^ n * g w)
        ((n : ℂ) * ((ρ : ℂ) - (ρ : ℂ)) ^ (n - 1) * 1 * g (ρ : ℂ) +
          ((ρ : ℂ) - (ρ : ℂ)) ^ n * deriv g (ρ : ℂ)) (ρ : ℂ) :=
      hp.mul hg.differentiableAt.hasDerivAt
    rw [hd.deriv, sub_self, zero_pow (by omega), zero_pow (by omega)]
    ring


/-- **Phase-rigid realizations contradict the anti-crystal law.** Let `Ξ(t) = Re G(t + ih)` with
`G` entire and nonzero on the line, positive phase speed `ω`, `ω` log-Lipschitz with constant `2/h'`
on `[T₀, ∞)`, and RH. Then the ordered ordinates are `(h'/2)`-rigid from some index on, which is
impossible. -/
theorem false_of_phase_rigid_realization {G : ℂ → ℂ} {h h' T₀ : ℝ} (hh' : 0 < h')
    (hGd : Differentiable ℂ G) (hne : ∀ t : ℝ, G ((t : ℂ) + h * I) ≠ 0)
    (hrep : ∀ t : ℝ, Xi t = (G ((t : ℂ) + h * I)).re) (hRH : RiemannHypothesis)
    (hωpos : ∀ t, 0 < phaseSpeed G h t)
    (hLL : ∀ s t, T₀ ≤ s → T₀ ≤ t →
      phaseSpeed G h s ≤ Real.exp (2 * |s - t| / h') * phaseSpeed G h t) : False := by
  obtain ⟨A, φ, hA, hφ, hAφ⟩ := GaloisForLFunctions.HTGeometry.exists_phase_rep hGd hne
  set ω := phaseSpeed G h with hωdef
  have hXi : ∀ t, Xi t = A t * Real.cos (φ t) := fun t => by rw [hrep t, hAφ t]
  set γ := xiOrderedPositiveOrdinate with hγ
  have hγzero : ∀ n, Xi (γ n) = 0 := by
    intro n
    have h1 := xi_half_add_orderedPositiveOrdinate_mul_I_eq_zero hRH n
    have h2 : XiC (γ n) = 0 := by
      rw [XiC]; convert h1 using 2; push_cast; ring
    rw [XiC_ofReal] at h2
    exact_mod_cast h2
  have hreal : ∀ y : ℝ, 0 < y → Xi y = 0 → ∃ m, γ m = y := by
    intro y hy hy0
    have hxi : xi (1 / 2 + (y : ℂ) * I) = 0 := by
      have h1 := XiC_ofReal y
      rw [hy0, Complex.ofReal_zero] at h1
      rw [XiC] at h1; convert h1 using 2
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
    have hqpos : 0 < (q.1 : ℂ).im := by rw [hq]; simpa using hy
    obtain ⟨m, hm⟩ := exists_xiOrderedPositiveZeroCopy_eq hqpos
    refine ⟨m, ?_⟩
    rw [hγ, ← xiOrderedPositiveZeroCopy_im_eq, hm, hq]
    simp
  have hgap0 : ∀ n, ∀ x ∈ Ioo (γ n) (γ (n + 1)), A x * Real.cos (φ x) ≠ 0 := by
    intro n x hx h0
    rw [← hXi] at h0
    have hx0 : 0 < x := lt_of_le_of_lt (xiOrderedPositiveOrdinate_nonneg n) hx.1
    obtain ⟨m, hm⟩ := hreal x hx0 h0
    rcases le_or_gt m n with hmn | hmn
    · have := xiOrderedPositiveOrdinate_monotone hmn; rw [← hγ] at this; linarith [hx.1]
    · have := xiOrderedPositiveOrdinate_monotone (show n + 1 ≤ m by omega)
      rw [← hγ] at this; linarith [hx.2]
  have hRHxi := riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH
  have hstrict : ∀ n, γ n < γ (n + 1) := by
    intro n
    rcases lt_or_eq_of_le (xiOrderedPositiveOrdinate_monotone (Nat.le_succ n)) with hlt | heq
    · exact hlt
    · exfalso
      set q₁ := xiOrderedPositiveZeroCopy n with hq₁
      set q₂ := xiOrderedPositiveZeroCopy (n + 1) with hq₂
      have hq12 : q₁ ≠ q₂ := fun h12 => by
        have := xiOrderedPositiveZeroCopy_injective h12; omega
      have hpt : ∀ k, ((xiOrderedPositiveZeroCopy k).1 : ℂ) = 1 / 2 + (γ k : ℂ) * I := by
        intro k
        apply Complex.ext
        · rw [hRHxi _ (xi_xiZeroCopy_eq_zero _)]; simp
        · rw [xiOrderedPositiveZeroCopy_im_eq]; simp [hγ]
      have heqC : (q₁.1 : ℂ) = (q₂.1 : ℂ) := by
        have hγeq : γ n = γ (n + 1) := heq
        rw [hq₁, hq₂, hpt n, hpt (n + 1), hγeq]
      have hcrit := deriv_xi_eq_zero_of_copies hq12 heqC
      rw [hq₁, hpt n] at hcrit
      have hd1 := hasDerivAt_Xi_xi (γ n)
      rw [hcrit, zero_mul, Complex.zero_re] at hd1
      have hd2 := hasDerivAt_Xi_of_realization hGd hrep (γ n)
      have hzero : (G ((γ n : ℂ) + h * I)).re = 0 := by rw [← hrep]; exact hγzero n
      exact re_deriv_ne_zero_of_realization (hne _) (hωpos _) hzero (hd2.unique hd1)
  -- rigidity above `T₀`
  set N₀ := (xiZeroCount T₀).toNat with hN₀
  have habove : ∀ n, N₀ ≤ n → T₀ ≤ γ n := by
    intro n hn
    by_contra hlt; push Not at hlt
    have := lt_toNat_xiZeroCount_iff.mpr hlt.le
    omega
  have hrig : ∀ n, N₀ ≤ n → ordinateGap (n + 1) ≤ ordinateGap n *
        Real.exp ((ordinateGap n + ordinateGap (n + 1)) / (h' / 2)) ∧
      ordinateGap n ≤ ordinateGap (n + 1) *
        Real.exp ((ordinateGap n + ordinateGap (n + 1)) / (h' / 2)) := by
    intro n hn
    have hz : ∀ k, A (γ k) * Real.cos (φ (γ k)) = 0 := fun k => by rw [← hXi]; exact hγzero k
    have hgr := GaloisForLFunctions.HTGeometry.gap_rigidity_of_phase_on hh' hA hφ hωpos hLL
      (habove n hn) (hstrict n) (hstrict (n + 1)) (hz n) (hz (n + 1)) (hz (n + 2)) (hgap0 n)
      (hgap0 (n + 1))
    have he : 2 * (γ (n + 2) - γ n) / h' = (ordinateGap n + ordinateGap (n + 1)) / (h' / 2) := by
      simp only [ordinateGap, hγ]
      field_simp
      ring
    rw [he] at hgr
    have e1 : γ (n + 2) - γ (n + 1) = ordinateGap (n + 1) := by simp only [ordinateGap, hγ]
    have e2 : γ (n + 1) - γ n = ordinateGap n := by simp only [ordinateGap, hγ]
    rw [e1, e2] at hgr
    exact hgr
  exact not_rigidOrdinates (half_pos hh') N₀
    ⟨fun n _ => hstrict n, fun n hn => (hrig n hn).1, fun n hn => (hrig n hn).2⟩

/-- **The gapless realization law.** For no `h > 0` is `Ξ(t) = Re G(t + ih)` on `ℝ` with `G` a
lower Pólya function. -/
theorem not_exists_lowerPolyaClass_realization {h : ℝ} (hh : 0 < h) :
    ¬ ∃ G : ℂ → ℂ, LowerPolyaClass G ∧ ∀ t : ℝ, Xi t = (G ((t : ℂ) + h * I)).re := by
  rintro ⟨G, hG, hrep⟩
  have hGd := hG.differentiable
  have hGa : G ((0 : ℝ) + h * I) ≠ 0 := by
    intro h0
    have := hrep 0
    rw [h0, Complex.zero_re] at this
    exact Xi_zero_pos.ne' this
  have hne : ∀ t : ℝ, G ((t : ℂ) + h * I) ≠ 0 := by
    intro t h0
    have := lowerPolyaClass_im_nonpos_of_eq_zero hG hGa h0
    simp at this
    linarith
  obtain ⟨A, φ, hA, hφ, hAφ⟩ := GaloisForLFunctions.HTGeometry.exists_phase_rep hGd hne
  have hLL := fun s t => hG.phaseSpeed_le_exp_mul hh hne s t
  have hXi : ∀ t, Xi t = A t * Real.cos (φ t) := fun t => by rw [hrep t, hAφ t]
  have hωpos : ∀ t, 0 < phaseSpeed G h t := by
    intro t₀
    by_contra hle
    push Not at hle
    have hz : ∀ s, phaseSpeed G h s = 0 := fun s => by
      have h1 := (hLL s t₀).2
      have : phaseSpeed G h t₀ = 0 := le_antisymm hle (hLL t₀ t₀).1
      rw [this, mul_zero] at h1
      have h3 := (hLL s s).1
      linarith
    have hconst : ∀ x y : ℝ, φ x = φ y := by
      refine is_const_of_deriv_eq_zero (fun x => (hφ x).differentiableAt) fun x => ?_
      rw [(hφ x).deriv, hz x, neg_zero]
    obtain ⟨t, -, ht⟩ := exists_Xi_zero_gt 0
    have h0 := Xi_zero_pos
    rw [hXi] at ht h0
    rw [hconst t 0] at ht
    have hc : Real.cos (φ 0) = 0 := (mul_eq_zero.mp ht).resolve_left (hA t).ne'
    rw [hc, mul_zero] at h0
    exact lt_irrefl _ h0
  exact false_of_phase_rigid_realization (T₀ := 0) hh hGd hne hrep
    (riemannHypothesis_of_lowerPolyaClass_realization hh hG hrep) hωpos
    (fun s t _ _ => (hLL s t).2)
end

end RHTower
