import Mathlib
import GaloisForLFunctions.EntireJetEvaluation

/-!
# The identity theorem through derivatives: entire functions with flat origin vanish

An entire function all of whose derivatives vanish at the origin is identically zero
(`entire_eq_zero_of_forall_iteratedDeriv_zero`).  If the analytic order at the origin is
infinite the function vanishes near the origin and the identity theorem spreads the zero over
the connected plane; a finite order `m` would exhibit the function as `z^m·g` with
`g(0) ≠ 0`, whose `m`-th derivative at the origin is `m!·g(0) ≠ 0`
(`iteratedDeriv_pow_mul_analytic`).

This is the bridge between the function register and the coefficient register of algebraic
differential equations: a differential-polynomial evaluation on the jets of an entire
function vanishes identically exactly when its countably many Taylor conditions at one point
vanish — the analytic input of coefficient-field normalization.
-/

namespace GaloisForLFunctions

/-- Eventual equality propagates through iterated derivatives. -/
theorem eventuallyEq_iteratedDeriv {f g : ℂ → ℂ} {x : ℂ} (h : f =ᶠ[nhds x] g) (n : ℕ) :
    iteratedDeriv n f =ᶠ[nhds x] iteratedDeriv n g := by
  induction n with
  | zero => simpa [iteratedDeriv_zero] using h
  | succ n ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    exact ih.deriv

/-- `dⁿ/dzⁿ (zⁿ·g)(0) = n!·g(0)` for `g` analytic at the origin. -/
theorem iteratedDeriv_pow_mul_analytic :
    ∀ (n : ℕ) {g : ℂ → ℂ}, AnalyticAt ℂ g 0 →
      iteratedDeriv n (fun z => z ^ n * g z) 0 = (Nat.factorial n : ℂ) * g 0 := by
  intro n
  induction n with
  | zero =>
    intro g _
    simp [iteratedDeriv_zero]
  | succ n ih =>
    intro g hg
    rw [iteratedDeriv_succ']
    have hev : deriv (fun z : ℂ => z ^ (n + 1) * g z)
        =ᶠ[nhds 0] fun z => z ^ n * (((n : ℂ) + 1) * g z + z * deriv g z) := by
      filter_upwards [hg.eventually_analyticAt] with z hz
      have hder : HasDerivAt (fun w : ℂ => w ^ (n + 1) * g w)
          ((((n : ℂ) + 1) * z ^ n) * g z + z ^ (n + 1) * deriv g z) z := by
        have hp : HasDerivAt (fun w : ℂ => w ^ (n + 1))
            (((n : ℂ) + 1) * z ^ n) z := by
          have h0 := hasDerivAt_pow (n + 1) z
          simpa [Nat.add_sub_cancel] using h0
        exact hp.mul hz.differentiableAt.hasDerivAt
      rw [hder.deriv]
      ring
    rw [(eventuallyEq_iteratedDeriv hev n).eq_of_nhds]
    have hg1 : AnalyticAt ℂ (fun z => ((n : ℂ) + 1) * g z + z * deriv g z) 0 :=
      (analyticAt_const.mul hg).add (analyticAt_id.mul hg.deriv)
    rw [ih hg1]
    simp only [zero_mul, add_zero]
    push_cast [Nat.factorial_succ]
    ring

/-- **Entire functions flat at the origin vanish**: if every iterated derivative of an entire
function vanishes at `0`, the function is identically zero. -/
theorem entire_eq_zero_of_forall_iteratedDeriv_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h : ∀ k, iteratedDeriv k f 0 = 0) : f = 0 := by
  have hA : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hA0 : AnalyticAt ℂ f 0 := hA 0 (Set.mem_univ 0)
  rcases eq_or_ne (analyticOrderAt f 0) ⊤ with htop | hne
  · have hev := analyticOrderAt_eq_top.mp htop
    have hfreq : ∃ᶠ z in nhdsWithin 0 {(0 : ℂ)}ᶜ, f z = 0 :=
      Filter.Eventually.frequently (hev.filter_mono nhdsWithin_le_nhds)
    have hEq := hA.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (Set.mem_univ 0) hfreq
    funext z
    exact hEq (Set.mem_univ z)
  · exfalso
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
    obtain ⟨g, hg, hg0, hevg⟩ := hA0.analyticOrderAt_eq_natCast.mp hm.symm
    have hev' : f =ᶠ[nhds 0] fun z => z ^ m * g z := by
      filter_upwards [hevg] with z hz
      simpa [sub_zero, smul_eq_mul] using hz
    have hd := (eventuallyEq_iteratedDeriv hev' m).eq_of_nhds
    rw [h m] at hd
    rw [iteratedDeriv_pow_mul_analytic m hg] at hd
    have hfact : (Nat.factorial m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    rcases mul_eq_zero.mp hd.symm with h1 | h1
    · exact hfact h1
    · exact hg0 h1

end GaloisForLFunctions

namespace GaloisForLFunctions

/-- **Differential algebraicity through Taylor conditions.**  For an entire function, being
differentially algebraic is equivalent to the existence of a nonzero differential polynomial
all of whose jet-evaluation derivatives vanish at one point: the identically-vanishing
functional relation and its countable family of Taylor conditions at the origin carry the
same information. -/
theorem differentiallyAlgebraic_iff_taylor_conditions {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) :
    DifferentiallyAlgebraic f ↔ ∃ (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ), P ≠ 0 ∧
      ∀ k, iteratedDeriv k (fun z => MvPolynomial.eval
        (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) P) 0 = 0 := by
  constructor
  · rintro ⟨n, P, hP0, hPz⟩
    refine ⟨n, P, hP0, fun k => ?_⟩
    have hfun : (fun z => MvPolynomial.eval
        (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) P) = fun _ => 0 :=
      funext hPz
    rw [hfun]
    simp
  · rintro ⟨n, P, hP0, hflat⟩
    refine ⟨n, P, hP0, fun z => ?_⟩
    have h0 := entire_eq_zero_of_forall_iteratedDeriv_zero
      (differentiable_jetEval hf n P) hflat
    exact congrFun h0 z

end GaloisForLFunctions
