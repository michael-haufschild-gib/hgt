/-
Ray-complete flat carriers are translation-faithful.

The finite translation algebra `A = ℂ[(ℂ,+)] = AddMonoidAlgebra ℂ ℂ` acts on generalized
Dirichlet carriers by `T_h f(s) = f(s+h)`.  A carrier `F(s) = ∑_{p} ∑_{m≥1} b_{p,m} e^{-m λ_p s}`
with `b_{p,m} ≠ 0` is **ray-complete** when its primitive frequencies `λ_p` are positive with
pairwise irrational ratios and every positive multiple of every ray occurs.

The analytic constraint ideal `I_an(F) = {P : P F ∈ ℂ(s)}` of such a carrier is captured, through
generalized-Dirichlet coefficient uniqueness, by the translation *characters*
`χ_λ(∑_j c_j T_{h_j}) = ∑_j c_j e^{-λ h_j}` (the algebra homs `A → ℂ` sending `T_h ↦ e^{-λ h}`):
a finite operator `P` rationalizes `F` iff `χ_{m λ_p}(P) = 0` for every ray `p` and multiple `m`.
This file formalizes the algebraic heart of the theorem: on an infinite set of positive
pairwise-incommensurable rays the joint kernel of the characters `{χ_{m λ_p}}` is trivial, so the
translation algebra acts faithfully.

Sections mirror the paper:
* `translationChar` / `translationChar_apply` — the characters of the translation algebra.
* `exists_injective_ray` — the aliasing lemma: on some ray the map `h ↦ e^{-λ_p h}` is injective on
  a given finite support.
* `translationChar_moments_eq_zero` — the ray-complete faithfulness theorem `I_an(F) = 0`.
* `annIdeal` / `rayComplete_annIdeal_eq_bot` — the same as the vanishing of the analytic ideal.
* `euler_translation_faithful` — the Euler logarithmic-derivative instance (`λ_p = log p`).
* `eulerJ` / `eulerJ_antitone` / `eulerJ_iInf_eq_bot` — the finite-stage ancestor filtration and its
  cofinal separation law `⋂_N J_N = 0`.
* `completion_injection` / `completedZeta_nonzero_class` — the completion-injection law and the
  completed-zeta instance, over an abstract module of carriers with a rational subspace.
-/
import Mathlib
import GaloisForLFunctions.RHTower.ZeroEstimate
import GaloisForLFunctions.RHTower.GelfondSchneider
import GaloisForLFunctions.RHTower.WeldZeroGenerator

open Complex

namespace GaloisForLFunctions.RHTower

/-! ### §1 The characters of the finite translation algebra -/

/-- The multiplicative character `h ↦ e^{-λ h}` on `Multiplicative ℂ`. -/
noncomputable def transChar (l : ℝ) : Multiplicative ℂ →* ℂ where
  toFun h := Complex.exp (-(l : ℂ) * Multiplicative.toAdd h)
  map_one' := by
    show Complex.exp (-(l : ℂ) * Multiplicative.toAdd (1 : Multiplicative ℂ)) = 1
    rw [show Multiplicative.toAdd (1 : Multiplicative ℂ) = (0 : ℂ) from rfl, mul_zero,
      Complex.exp_zero]
  map_mul' x y := by
    show Complex.exp (-(l : ℂ) * Multiplicative.toAdd (x * y))
        = Complex.exp (-(l : ℂ) * Multiplicative.toAdd x)
          * Complex.exp (-(l : ℂ) * Multiplicative.toAdd y)
    rw [show Multiplicative.toAdd (x * y) = Multiplicative.toAdd x + Multiplicative.toAdd y from rfl,
      mul_add, Complex.exp_add]

@[simp] lemma transChar_ofAdd (l : ℝ) (h : ℂ) :
    transChar l (Multiplicative.ofAdd h) = Complex.exp (-(l : ℂ) * h) := rfl

/-- The translation-algebra character `χ_λ : A → ℂ`, the algebra hom sending `T_h ↦ e^{-λ h}`.
On `P = ∑_j c_j T_{h_j}` it evaluates to `∑_j c_j e^{-λ h_j}`. -/
noncomputable def translationChar (l : ℝ) : AddMonoidAlgebra ℂ ℂ →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ ℂ (transChar l)

/-- Explicit value of the translation character as the finite exponential sum over the support. -/
lemma translationChar_apply (l : ℝ) (P : AddMonoidAlgebra ℂ ℂ) :
    translationChar l P =
      ∑ h ∈ P.coeff.support, P.coeff h * Complex.exp (-(l : ℂ) * h) := by
  rw [translationChar, AddMonoidAlgebra.lift_apply]
  rw [show (Finsupp.sum P.coeff fun a b => b • (transChar l) (Multiplicative.ofAdd a))
        = ∑ h ∈ P.coeff.support,
            (P.coeff h) • (transChar l) (Multiplicative.ofAdd h) from rfl]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [transChar_ofAdd, smul_eq_mul]

/-- The character on a single translation `T_h`: `χ_λ(T_h) = e^{-λ h}`. -/
lemma translationChar_single (l : ℝ) (h : ℂ) :
    translationChar l (AddMonoidAlgebra.single h 1) = Complex.exp (-(l : ℂ) * h) := by
  rw [translationChar, AddMonoidAlgebra.lift_single, transChar_ofAdd, one_smul]

/-! ### §2 The aliasing lemma -/

/-- **Aliasing lemma.**  Given an infinite family of positive rays with pairwise irrational ratios,
for every finite set `S` of shifts there is a ray `p` on which `h ↦ e^{-λ_p h}` is injective over
`S`.  A collision `e^{-λ_p a} = e^{-λ_p b}` means `λ_p (b - a) ∈ 2πi ℤ`; the same pair of shifts
cannot collide on two rays without making `λ_p / λ_q` rational, so each of the finitely many pairs
excludes at most one ray while the family is infinite. -/
theorem exists_injective_ray {ι : Type*} [Infinite ι] (l : ι → ℝ)
    (hpos : ∀ p, 0 < l p) (hirr : ∀ p q, p ≠ q → Irrational (l p / l q))
    (S : Finset ℂ) :
    ∃ p : ι, ∀ a ∈ S, ∀ b ∈ S,
      Complex.exp (-(l p : ℂ) * a) = Complex.exp (-(l p : ℂ) * b) → a = b := by
  classical
  by_contra hcon
  have hcon' : ∀ p : ι, ∃ a ∈ S, ∃ b ∈ S,
      Complex.exp (-(l p : ℂ) * a) = Complex.exp (-(l p : ℂ) * b) ∧ a ≠ b := by
    intro p
    by_contra hp
    exact hcon ⟨p, fun a ha b hb hEq => by
      by_contra hab
      exact hp ⟨a, ha, b, hb, hEq, hab⟩⟩
  choose a ha b hb hR using hcon'
  set f : ι → (S ×ˢ S : Finset (ℂ × ℂ)) :=
    fun p => ⟨(a p, b p), Finset.mem_product.mpr ⟨ha p, hb p⟩⟩ with hf
  obtain ⟨p, q, hpqne, hpq⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hval : (a p, b p) = (a q, b q) := by
    simpa [hf, Subtype.ext_iff] using hpq
  rw [Prod.mk.injEq] at hval
  obtain ⟨haeq, hbeq⟩ := hval
  -- alias relation on ray p
  obtain ⟨n, hn⟩ := (Complex.exp_eq_exp_iff_exists_int).mp (hR p).1
  have hp_rel : (l p : ℂ) * (b p - a p) = (n : ℂ) * (2 * (Real.pi : ℂ) * I) := by
    linear_combination hn
  -- alias relation on ray q, using a q = a p and b q = b p
  have habq : Complex.exp (-(l q : ℂ) * a p) = Complex.exp (-(l q : ℂ) * b p) := by
    have hcopy := (hR q).1; rw [← haeq, ← hbeq] at hcopy; exact hcopy
  obtain ⟨n', hn'⟩ := (Complex.exp_eq_exp_iff_exists_int).mp habq
  have hq_rel : (l q : ℂ) * (b p - a p) = (n' : ℂ) * (2 * (Real.pi : ℂ) * I) := by
    linear_combination hn'
  -- nonvanishing facts
  have hd : (b p - a p) ≠ 0 := sub_ne_zero.mpr (Ne.symm (hR p).2)
  have hlp : (l p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hpos p).ne'
  have hlq : (l q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hpos q).ne'
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [Int.cast_zero, zero_mul] at hp_rel
    rcases mul_eq_zero.mp hp_rel with h | h
    · exact hlp h
    · exact hd h
  have hn0' : n' ≠ 0 := by
    rintro rfl
    rw [Int.cast_zero, zero_mul] at hq_rel
    rcases mul_eq_zero.mp hq_rel with h | h
    · exact hlq h
    · exact hd h
  -- cancel the common shift difference: n' λ_p = n λ_q
  have hcancel : (n' : ℂ) * (l p : ℂ) = (n : ℂ) * (l q : ℂ) := by
    have e1 : (n' : ℂ) * ((l p : ℂ) * (b p - a p))
        = (n : ℂ) * ((l q : ℂ) * (b p - a p)) := by
      rw [hp_rel, hq_rel]; ring
    have e2 : ((n' : ℂ) * (l p : ℂ)) * (b p - a p)
        = ((n : ℂ) * (l q : ℂ)) * (b p - a p) := by
      rw [← mul_assoc, ← mul_assoc] at e1; exact e1
    exact mul_right_cancel₀ hd e2
  have hcastR : (n' : ℝ) * (l p) = (n : ℝ) * (l q) := by exact_mod_cast hcancel
  -- rationality of λ_p / λ_q contradicts irrationality
  have hratio : l p / l q = (n : ℝ) / (n' : ℝ) := by
    rw [div_eq_div_iff (hpos q).ne' (Int.cast_ne_zero.mpr hn0')]
    linear_combination hcastR
  have hirrp : Irrational (l p / l q) := hirr p q hpqne
  rw [hratio] at hirrp
  have hcastQ : (((n : ℚ) / (n' : ℚ) : ℚ) : ℝ) = (n : ℝ) / (n' : ℝ) := by push_cast; ring
  rw [← hcastQ] at hirrp
  exact (Rat.not_irrational _) hirrp

/-! ### §3 The Vandermonde separation core -/

/-- **Finite Vandermonde separation.**  If `z` is injective on a finite set `S` and the weighted
power moments `∑_{h∈S} c_h (z h)^k` vanish for `k = 0,…,|S|-1`, then every weight `c_h` vanishes.
The first `|S|` moments form a Vandermonde system at the distinct nodes `z h`. -/
theorem finset_moments_eq_zero {S : Finset ℂ} (z c : ℂ → ℂ)
    (hz : ∀ a ∈ S, ∀ b ∈ S, z a = z b → a = b)
    (hmom : ∀ k : ℕ, k < S.card → ∑ h ∈ S, c h * (z h) ^ k = 0) :
    ∀ h ∈ S, c h = 0 := by
  classical
  set e : (↥S) ≃ Fin S.card := Fintype.equivFinOfCardEq (Fintype.card_coe S)
  have hμinj : Function.Injective (fun j : Fin S.card => z ↑(e.symm j)) := by
    intro i j hij
    have hval := hz (↑(e.symm i)) (e.symm i).2 (↑(e.symm j)) (e.symm j).2 hij
    exact e.symm.injective (Subtype.ext hval)
  have hmomFin : ∀ k : Fin S.card,
      ∑ j : Fin S.card, (fun j => c ↑(e.symm j)) j
        * ((fun j => z ↑(e.symm j)) j) ^ (k : ℕ) = 0 := by
    intro k
    have step1 : ∑ j : Fin S.card, c ↑(e.symm j) * (z ↑(e.symm j)) ^ (k : ℕ)
        = ∑ x : ↥S, c ↑x * (z ↑x) ^ (k : ℕ) :=
      Fintype.sum_equiv e.symm _ _ (fun j => rfl)
    have step2 : ∑ x : ↥S, c ↑x * (z ↑x) ^ (k : ℕ) = ∑ h ∈ S, c h * (z h) ^ (k : ℕ) :=
      Finset.sum_coe_sort S (fun h => c h * (z h) ^ (k : ℕ))
    show ∑ j : Fin S.card, c ↑(e.symm j) * (z ↑(e.symm j)) ^ (k : ℕ) = 0
    rw [step1, step2]
    exact hmom (k : ℕ) k.isLt
  have hres := vandermonde_moments_eq_zero_of_injective hμinj hmomFin
  intro h hh
  have hz0 : (fun j : Fin S.card => c ↑(e.symm j)) (e ⟨h, hh⟩) = 0 := by
    rw [hres]; rfl
  simpa only [Equiv.symm_apply_apply] using hz0

/-- **Ray-complete translation faithfulness (`I_an(F) = 0`).**  Let the positive rays `λ_p`, indexed
by an infinite set, have pairwise irrational ratios.  If a finite translation operator `P` has
`χ_{m λ_p}(P) = 0` for every ray `p` and multiple `m ≥ 1` — equivalently `P F` is rational for the
ray-complete carrier `F` — then `P = 0`.  The finite translation algebra acts faithfully. -/
theorem translationChar_moments_eq_zero {ι : Type*} [Infinite ι] (l : ι → ℝ)
    (hpos : ∀ p, 0 < l p) (hirr : ∀ p q, p ≠ q → Irrational (l p / l q))
    (P : AddMonoidAlgebra ℂ ℂ)
    (hvanish : ∀ (p : ι) (m : ℕ), 1 ≤ m → translationChar ((m : ℝ) * l p) P = 0) :
    P = 0 := by
  classical
  obtain ⟨p, hinj⟩ := exists_injective_ray l hpos hirr P.coeff.support
  have hmom : ∀ m : ℕ, 1 ≤ m →
      ∑ h ∈ P.coeff.support,
        P.coeff h * (Complex.exp (-(l p : ℂ) * h)) ^ m = 0 := by
    intro m hm
    have h0 := hvanish p m hm
    rw [translationChar_apply] at h0
    rw [← h0]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    congr 1
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast; ring
  have hall : ∀ h ∈ P.coeff.support,
      P.coeff h * Complex.exp (-(l p : ℂ) * h) = 0 := by
    refine finset_moments_eq_zero (fun h => Complex.exp (-(l p : ℂ) * h))
      (fun h => P.coeff h * Complex.exp (-(l p : ℂ) * h)) hinj ?_
    intro k _
    have hstep : ∑ h ∈ P.coeff.support,
          (P.coeff h * Complex.exp (-(l p : ℂ) * h)) *
            (Complex.exp (-(l p : ℂ) * h)) ^ k
        = ∑ h ∈ P.coeff.support,
            P.coeff h * (Complex.exp (-(l p : ℂ) * h)) ^ (k + 1) := by
      refine Finset.sum_congr rfl (fun h _ => ?_)
      rw [pow_succ]; ring
    rw [hstep]
    exact hmom (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
  apply AddMonoidAlgebra.coeff_injective
  refine Finsupp.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem ?_)
  intro h hh
  rcases mul_eq_zero.mp (hall h hh) with h1 | h2
  · exact (Finsupp.mem_support_iff.mp hh) h1
  · exact Complex.exp_ne_zero _ h2

/-! ### §4 The analytic constraint ideal -/

/-- The kernel ideal of a single translation character. -/
noncomputable def translationCharKer (l : ℝ) : Ideal (AddMonoidAlgebra ℂ ℂ) :=
  RingHom.ker (translationChar l).toRingHom

/-- The analytic constraint ideal `I_an` of a carrier with frequency set `F`: the finite translation
operators annihilated by every character `χ_l`, `l ∈ F`.  For a ray-complete carrier this coincides,
via generalized-Dirichlet uniqueness, with `{P : P F ∈ ℂ(s)}`. -/
noncomputable def annIdeal (F : Set ℝ) : Ideal (AddMonoidAlgebra ℂ ℂ) :=
  ⨅ l : F, translationCharKer l.val

lemma mem_annIdeal {F : Set ℝ} {P : AddMonoidAlgebra ℂ ℂ} :
    P ∈ annIdeal F ↔ ∀ l ∈ F, translationChar l P = 0 := by
  rw [annIdeal, Ideal.mem_iInf]
  constructor
  · intro h l hl
    have h2 := h ⟨l, hl⟩
    rw [translationCharKer, RingHom.mem_ker] at h2
    exact h2
  · intro h l
    rw [translationCharKer, RingHom.mem_ker]
    exact h l.1 l.2

lemma annIdeal_antitone {F G : Set ℝ} (h : F ⊆ G) : annIdeal G ≤ annIdeal F := by
  intro P hP
  rw [mem_annIdeal] at hP ⊢
  exact fun l hl => hP l (h hl)

/-- **Ray completeness is load-bearing (converse boundary).**  If the frequency set consists of the
multiples of a *single* positive ray `λ`, the analytic constraint ideal is nonzero: the operator
`T_{2πi/λ} - 1` annihilates every multiple `m λ` since `e^{-(m λ)(2πi/λ)} = e^{-2πi m} = 1`, and it
is nonzero.  Faithfulness `(8)` therefore genuinely requires infinitely many incommensurable rays. -/
theorem annIdeal_single_ray_ne_bot (lam : ℝ) (hlam : 0 < lam) :
    annIdeal {x : ℝ | ∃ m : ℕ, 1 ≤ m ∧ x = (m : ℝ) * lam} ≠ ⊥ := by
  have hlamC : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam.ne'
  have h2pi : (2 * (Real.pi : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  set h : ℂ := (2 * (Real.pi : ℂ) * I) / (lam : ℂ) with hh
  have hh0 : h ≠ 0 := by rw [hh]; exact div_ne_zero h2pi hlamC
  set g : AddMonoidAlgebra ℂ ℂ := AddMonoidAlgebra.single h 1 - 1 with hg
  have hmem : g ∈ annIdeal {x : ℝ | ∃ m : ℕ, 1 ≤ m ∧ x = (m : ℝ) * lam} := by
    rw [mem_annIdeal]
    rintro x ⟨m, hm, rfl⟩
    rw [hg, map_sub, translationChar_single, map_one]
    have hkey : (-(((m : ℝ) * lam : ℝ) : ℂ) * h) = ((-m : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by
      rw [hh]; field_simp; push_cast; ring
    rw [hkey, Complex.exp_int_mul_two_pi_mul_I, sub_self]
  have hne : g ≠ 0 := by
    rw [hg, sub_ne_zero]
    intro heq
    have hcoe : (AddMonoidAlgebra.single h (1 : ℂ)).coeff h =
        (1 : AddMonoidAlgebra ℂ ℂ).coeff h :=
      congrArg (fun f : AddMonoidAlgebra ℂ ℂ => f.coeff h) heq
    rw [AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.one_def,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply,
      if_pos rfl, if_neg hh0.symm] at hcoe
    exact one_ne_zero hcoe
  intro hbot
  rw [hbot, Ideal.mem_bot] at hmem
  exact hne hmem

/-- **`I_an(F) = 0` for ray-complete `F`, ideal form.**  If the frequency set `F` contains every
positive multiple of an infinite set of positive pairwise-incommensurable rays, its analytic
constraint ideal is trivial. -/
theorem rayComplete_annIdeal_eq_bot {ι : Type*} [Infinite ι] (l : ι → ℝ)
    (hpos : ∀ p, 0 < l p) (hirr : ∀ p q, p ≠ q → Irrational (l p / l q))
    {F : Set ℝ} (hF : ∀ (p : ι) (m : ℕ), 1 ≤ m → ((m : ℝ) * l p) ∈ F) :
    annIdeal F = ⊥ := by
  rw [eq_bot_iff]
  intro P hP
  rw [Ideal.mem_bot]
  rw [mem_annIdeal] at hP
  exact translationChar_moments_eq_zero l hpos hirr P (fun p m hm => hP _ (hF p m hm))

/-! ### §5 The Euler logarithmic-derivative instance -/

/-- **Euler translation faithfulness.**  The primitive frequencies `λ_p = log p` are positive with
pairwise irrational ratios (`log p / log q ∉ ℚ` since `p^a = q^b` is impossible), so the Euler
carrier `-ζ'/ζ = ∑_p ∑_{m≥1} (log p) e^{-m (log p) s}` — and every derivative — is
translation-faithful: no nonzero finite translation operator sends it into `ℂ(s)`. -/
theorem euler_translation_faithful (P : AddMonoidAlgebra ℂ ℂ)
    (hvanish : ∀ (p : ℕ), p.Prime → ∀ (m : ℕ), 1 ≤ m →
      translationChar ((m : ℝ) * Real.log p) P = 0) :
    P = 0 := by
  refine translationChar_moments_eq_zero (ι := Nat.Primes) (fun p => Real.log (p : ℕ))
    (fun p => Real.log_pos (by exact_mod_cast p.2.one_lt))
    (fun p q hpq => irrational_log_ratio q.2 p.2 (fun h => hpq (Subtype.ext h.symm))) P ?_
  intro p m hm
  exact hvanish (p : ℕ) p.2 m hm

/-- The Euler frequency set, all prime-power logs `{m·log p}`. -/
def eulerLogFreq : Set ℝ := {x : ℝ | ∃ p : ℕ, p.Prime ∧ ∃ m : ℕ, 1 ≤ m ∧ x = (m : ℝ) * Real.log p}

/-- **`I_an(-ζ'/ζ) = 0`.**  The analytic constraint ideal of the Euler logarithmic-derivative carrier
is trivial. -/
theorem eulerLogDeriv_annIdeal_eq_bot : annIdeal eulerLogFreq = ⊥ := by
  refine rayComplete_annIdeal_eq_bot (ι := Nat.Primes) (fun p => Real.log (p : ℕ))
    (fun p => Real.log_pos (by exact_mod_cast p.2.one_lt))
    (fun p q hpq => irrational_log_ratio q.2 p.2 (fun h => hpq (Subtype.ext h.symm))) ?_
  intro p m hm
  exact ⟨(p : ℕ), p.2, m, hm, rfl⟩

/-- **Euler flat-tower / zeta wiring.**  On `Re s > 1` the zero-generating function `-ζ'/ζ` is the
von Mangoldt Dirichlet series `∑ Λ(n) n^{-s}`, whose frequencies `{log n : Λ(n) ≠ 0}` are exactly
the prime-power logs `{m·log p}`; and on that frequency data the finite translation algebra acts
faithfully.  This is the concrete instance of the ray-complete theorem for the actual zeta object. -/
theorem zeta_logDeriv_translation_faithful {s : ℂ} (hs : 1 < s.re) :
    (-deriv riemannZeta s / riemannZeta s
        = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s)
      ∧ (∀ P : AddMonoidAlgebra ℂ ℂ,
          (∀ (p : ℕ), p.Prime → ∀ (m : ℕ), 1 ≤ m →
            translationChar ((m : ℝ) * Real.log p) P = 0) → P = 0) :=
  ⟨(zeta_logDeriv_frequencies_weld hs).1, fun P h => euler_translation_faithful P h⟩

/-! ### §8 The finite-stage ancestor filtration -/

/-- The frequency set of the prime cutoff `E_N = ∑_{p ≤ N} ∑_{m≥1} (log p) p^{-ms}`. -/
def eulerFreqBelow (N : ℕ) : Set ℝ :=
  {x : ℝ | ∃ p : ℕ, p.Prime ∧ p ≤ N ∧ ∃ m : ℕ, 1 ≤ m ∧ x = (m : ℝ) * Real.log p}

/-- The finite-stage annihilator ideal `J_N = I_an(E_N)`. -/
noncomputable def eulerJ (N : ℕ) : Ideal (AddMonoidAlgebra ℂ ℂ) := annIdeal (eulerFreqBelow N)

lemma eulerFreqBelow_mono {N M : ℕ} (h : N ≤ M) : eulerFreqBelow N ⊆ eulerFreqBelow M := by
  rintro x ⟨p, hp, hpN, m, hm, rfl⟩
  exact ⟨p, hp, le_trans hpN h, m, hm, rfl⟩

/-- **Decreasing filtration.**  `J_M ⊆ J_N` for `M ≥ N`: a larger cutoff imposes more character
constraints, hence a smaller annihilator. -/
theorem eulerJ_antitone {N M : ℕ} (h : N ≤ M) : eulerJ M ≤ eulerJ N :=
  annIdeal_antitone (eulerFreqBelow_mono h)

/-- **Cofinal separation law `⋂_N J_N = 0`.**  Every prime cutoff carries explicit finite
translation constraints, but no nonzero constraint survives all cutoffs: the Euler carrier is
cofinally cutoff-faithful.  This is the finite-to-infinite content of the theorem. -/
theorem eulerJ_iInf_eq_bot : (⨅ N, eulerJ N) = ⊥ := by
  rw [eq_bot_iff]
  intro P hP
  rw [Ideal.mem_bot]
  rw [Ideal.mem_iInf] at hP
  apply euler_translation_faithful
  intro p hp m hm
  have hPN := hP p
  rw [eulerJ, mem_annIdeal] at hPN
  exact hPN ((m : ℝ) * Real.log p) ⟨p, hp, le_refl p, m, hm, rfl⟩

/-! ### §6–§7 The completion-injection law (abstract carrier module) -/

section Completion

variable {V : Type*} [AddCommGroup V] [Module (AddMonoidAlgebra ℂ ℂ) V]
variable (ratl : Submodule (AddMonoidAlgebra ℂ ℂ) V)

/-- **Completion-injection law.**  Let `a` be a carrier with a complete formal shadow, and `e` a flat
carrier whose analytic constraint ideal is `0` (`hflat`).  If a finite operator `P` rationalizes `a`
(`hPa`) and its class in `Q_flat(a+e)` vanishes (`hcls : P(a+e)` rational), then `P e = P(a+e) - P a`
is rational, so `hflat` forces `P = 0`.  The archimedean constraint on `a` therefore injects into the
flat defect of `a + e`. -/
theorem completion_injection (a e : V) (P : AddMonoidAlgebra ℂ ℂ)
    (hPa : P • a ∈ ratl) (hcls : P • (a + e) ∈ ratl)
    (hflat : ∀ Q : AddMonoidAlgebra ℂ ℂ, Q • e ∈ ratl → Q = 0) : P = 0 := by
  apply hflat
  have hPe : P • e = P • (a + e) - P • a := by rw [smul_add]; abel
  rw [hPe]
  exact ratl.sub_mem hcls hPa

/-- **Completed-zeta instance.**  Write `Θ_Ξ = a_∞ - E'` for the completed logarithmic-derivative
tower.  The archimedean trigamma recurrence makes `(T_2 - 1) a_∞` rational (`hRat`); the Euler flat
source `E'` has trivial analytic ideal (`hEflat`, an instance of `eulerLogDeriv_annIdeal_eq_bot`).
Then `(T_2 - 1) Θ_Ξ` is *not* rational: the finite archimedean constraint `T_2 - 1` survives as a
nonzero flat-defect class of the completed object. -/
theorem completedZeta_nonzero_class (a_inf e : V)
    (hRat : (AddMonoidAlgebra.single (2 : ℂ) (1 : ℂ) - 1 : AddMonoidAlgebra ℂ ℂ) • a_inf ∈ ratl)
    (hEflat : ∀ Q : AddMonoidAlgebra ℂ ℂ, Q • e ∈ ratl → Q = 0) :
    ¬ ((AddMonoidAlgebra.single (2 : ℂ) (1 : ℂ) - 1 : AddMonoidAlgebra ℂ ℂ) • (a_inf - e) ∈ ratl) := by
  intro hcls
  have hne : (AddMonoidAlgebra.single (2 : ℂ) (1 : ℂ) - 1 : AddMonoidAlgebra ℂ ℂ) ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have hcoe : (AddMonoidAlgebra.single (2 : ℂ) (1 : ℂ)).coeff (2 : ℂ)
        = (1 : AddMonoidAlgebra ℂ ℂ).coeff (2 : ℂ) :=
      congrArg (fun f : AddMonoidAlgebra ℂ ℂ => f.coeff (2 : ℂ)) h
    rw [AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.one_def,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply,
      if_pos rfl, if_neg (by norm_num : ¬ (0 : ℂ) = 2)] at hcoe
    exact one_ne_zero hcoe
  apply hne
  refine completion_injection ratl a_inf (-e) _ hRat ?_ ?_
  · rw [← sub_eq_add_neg]; exact hcls
  · intro Q hQ
    apply hEflat Q
    rw [smul_neg] at hQ
    exact (neg_mem_iff).mp hQ

end Completion

end GaloisForLFunctions.RHTower
