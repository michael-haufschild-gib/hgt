import Mathlib

/-!
# Contractive scattering positivity is blind to the position of zeros

The scattering coefficient of the modular surface, `φ(s) = Λ(2s − 1)/Λ(2s)`, has its zeros in
`Re s > 1/2` at `s = (1 + ρ)/2`; RH puts them on `Re s = 3/4`. In the Gauss–Mayer parameter `w = 2s`
these are the events `ζ(w) = 0` (`GaussMayerScatteringMultiplicity`). The positivity that the
hyperbolic geometry supplies (Maass–Selberg, Lax–Phillips, the Gauss–Mayer Cauchy contraction) is
centred on the unitary line `Re s = 1/2`, i.e. `Re w = 1`: unitarity there and contractivity to the
right, which is positivity of the Schur form

`Σ_{i,j} c_i c̄_j (1 − φ(s_i) φ(s_j)^*) / (s_i + s̄_j − 1)`,  `Re s_i > 1/2`.

Its reflection is `s ↦ 1 − s̄`; the reflection of the zeta events is the arithmetic one,
`w ↦ 1 − w̄`, about `Re w = 1/2`, which is not a symmetry of the transfer operator.

This module shows that the Schur positivity cannot see where the zeros are. For `Re a > 1/2` let
`B_a(s) = (s − a)/(s − (1 − ā))` and `P_a = B_a B_ā`. Then `ψ = φ P_a`

* satisfies `ψ(s) ψ(1 − s) = φ(s) φ(1 − s)` (`blaschkePair_mul_one_sub`) and `ψ(s̄) = ψ(s)^*` when
  `φ` does (`blaschkePair_conj`),
* has `|ψ| = |φ|` on `Re s = 1/2` (`norm_halfBlaschke_of_re_eq_half`) and `|ψ| ≤ |φ|` to the
  right (`norm_halfBlaschke_le_one`),
* has Schur form equal to that of `φ` plus a nonnegative square (`schurForm_mul_halfBlaschke`),
* and vanishes at `a` and `ā`, anywhere in the half-plane (`scattering_positivity_blind_to_zeros`).

So every inequality of this type that `φ` satisfies is satisfied by a coefficient with zeros off
`Re s = 3/4`: such positivity localizes the events to a half-plane and no further.
-/

open ComplexConjugate Finset

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

noncomputable section

/-- The Blaschke factor of the half-plane `Re s > 1/2` vanishing at `a`; its pole `1 − ā` is the
mirror image of `a` in the line `Re s = 1/2`. -/
def halfBlaschke (a s : ℂ) : ℂ := (s - a) / (s - (1 - conj a))

/-- A conjugate pair of half-plane Blaschke factors. -/
def blaschkePair (a s : ℂ) : ℂ := halfBlaschke a s * halfBlaschke (conj a) s

/-- The Schur form of `φ` on the nodes `s` with coefficients `c`. -/
def schurForm {n : ℕ} (φ : ℂ → ℂ) (s c : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, c i * conj (c j) * ((1 - φ (s i) * conj (φ (s j))) / (s i + conj (s j) - 1))

theorem sub_mirror_ne_zero {a s : ℂ} (ha : 1 / 2 < a.re) (hs : 1 / 2 ≤ s.re) :
    s - (1 - conj a) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, Complex.zero_re] at this
  linarith

/-- `|s − (1 − ā)|² − |s − a|² = (2 Re s − 1)(2 Re a − 1)`. -/
theorem normSq_sub_mirror_sub_normSq (a s : ℂ) :
    Complex.normSq (s - (1 - conj a)) - Complex.normSq (s - a) =
      (2 * s.re - 1) * (2 * a.re - 1) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.conj_re, Complex.conj_im]
  ring

theorem norm_halfBlaschke_of_re_eq_half {a s : ℂ} (ha : 1 / 2 < a.re) (hs : s.re = 1 / 2) :
    ‖halfBlaschke a s‖ = 1 := by
  have hne := sub_mirror_ne_zero ha hs.ge
  have h := normSq_sub_mirror_sub_normSq a s
  rw [hs] at h
  have heq : Complex.normSq (s - a) = Complex.normSq (s - (1 - conj a)) := by linarith
  have heq' : ‖s - a‖ = ‖s - (1 - conj a)‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (s - a)), ← Real.sqrt_sq (norm_nonneg (s - (1 - conj a))),
      ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, heq]
  unfold halfBlaschke
  rw [norm_div, heq', div_self (norm_ne_zero_iff.mpr hne)]

theorem norm_halfBlaschke_le_one {a s : ℂ} (ha : 1 / 2 < a.re) (hs : 1 / 2 ≤ s.re) :
    ‖halfBlaschke a s‖ ≤ 1 := by
  have hne := sub_mirror_ne_zero ha hs
  have h := normSq_sub_mirror_sub_normSq a s
  have hle : Complex.normSq (s - a) ≤ Complex.normSq (s - (1 - conj a)) := by
    nlinarith
  have hle' : ‖s - a‖ ≤ ‖s - (1 - conj a)‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (s - a)), ← Real.sqrt_sq (norm_nonneg (s - (1 - conj a))),
      ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    exact Real.sqrt_le_sqrt hle
  unfold halfBlaschke
  rw [norm_div]
  exact div_le_one_of_le₀ hle' (norm_nonneg _)

/-- **The Schur kernel of a Blaschke factor has rank one.**
`1 − B_a(s) B_a(t)^* = (2 Re a − 1)(s + t̄ − 1) / ((s − (1 − ā))(t − (1 − ā))^*)`. -/
theorem one_sub_halfBlaschke_mul_conj (a s t : ℂ) (hs : s - (1 - conj a) ≠ 0)
    (ht : t - (1 - conj a) ≠ 0) :
    1 - halfBlaschke a s * conj (halfBlaschke a t) =
      ((2 * a.re - 1 : ℝ) : ℂ) * (s + conj t - 1) /
        ((s - (1 - conj a)) * conj (t - (1 - conj a))) := by
  have ht' : conj (t - (1 - conj a)) ≠ 0 := (map_ne_zero _).mpr ht
  have hre : ((2 * a.re - 1 : ℝ) : ℂ) = a + conj a - 1 := by
    rw [Complex.add_conj]; push_cast; ring
  unfold halfBlaschke
  rw [map_div₀, hre]
  field_simp
  simp only [map_sub, map_one, Complex.conj_conj]
  ring

private theorem schur_term_aux (A x y r D e f c d : ℂ) (hD : D ≠ 0) (he : e ≠ 0) (hf : f ≠ 0) :
    c * d * ((A + x * y * (r * D / (e * f))) / D) = c * d * (A / D) + r * (c * x / e * (d * y / f)) := by
  field_simp

/-- **Multiplying by a Blaschke factor adds a nonnegative square to the Schur form.** -/
theorem schurForm_mul_halfBlaschke {n : ℕ} (φ : ℂ → ℂ) (s c : Fin n → ℂ) {a : ℂ}
    (ha : 1 / 2 < a.re) (hs : ∀ i, 1 / 2 < (s i).re) :
    schurForm (fun z => φ z * halfBlaschke a z) s c =
      schurForm φ s c + ((2 * a.re - 1) * Complex.normSq
        (∑ i, c i * φ (s i) / (s i - (1 - conj a))) : ℝ) := by
  have he : ∀ i, s i - (1 - conj a) ≠ 0 := fun i => sub_mirror_ne_zero ha (hs i).le
  have hD : ∀ i j, s i + conj (s j) - 1 ≠ 0 := fun i j h => by
    have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re,
      Complex.zero_re] at this
    linarith [hs i, hs j]
  have hterm : ∀ i j, c i * conj (c j) *
      ((1 - φ (s i) * halfBlaschke a (s i) * conj (φ (s j) * halfBlaschke a (s j))) /
        (s i + conj (s j) - 1)) =
      c i * conj (c j) * ((1 - φ (s i) * conj (φ (s j))) / (s i + conj (s j) - 1)) +
        ((2 * a.re - 1 : ℝ) : ℂ) * (c i * φ (s i) / (s i - (1 - conj a)) *
          (conj (c j) * conj (φ (s j)) / conj (s j - (1 - conj a)))) := by
    intro i j
    have hk := one_sub_halfBlaschke_mul_conj a (s i) (s j) (he i) (he j)
    have hsplit : 1 - φ (s i) * halfBlaschke a (s i) * conj (φ (s j) * halfBlaschke a (s j)) =
        (1 - φ (s i) * conj (φ (s j))) +
          φ (s i) * conj (φ (s j)) * (1 - halfBlaschke a (s i) * conj (halfBlaschke a (s j))) := by
      rw [map_mul]; ring
    rw [hsplit, hk]
    exact schur_term_aux _ _ _ _ _ _ _ _ _ (hD i j) (he i) ((map_ne_zero _).mpr (he j))
  unfold schurForm
  simp only [hterm, sum_add_distrib]
  congr 1
  rw [Complex.ofReal_mul, ← Complex.mul_conj, map_sum, sum_mul_sum, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  simp only [map_div₀, map_mul]

/-- The real part of the Schur form does not decrease under a Blaschke factor. -/
theorem re_schurForm_le_mul_halfBlaschke {n : ℕ} (φ : ℂ → ℂ) (s c : Fin n → ℂ) {a : ℂ}
    (ha : 1 / 2 < a.re) (hs : ∀ i, 1 / 2 < (s i).re) :
    (schurForm φ s c).re ≤ (schurForm (fun z => φ z * halfBlaschke a z) s c).re := by
  rw [schurForm_mul_halfBlaschke φ s c ha hs, Complex.add_re, Complex.ofReal_re]
  have : 0 ≤ (2 * a.re - 1) * Complex.normSq (∑ i, c i * φ (s i) / (s i - (1 - conj a))) :=
    mul_nonneg (by linarith) (Complex.normSq_nonneg _)
  linarith

/-- The Blaschke pair satisfies the scattering functional equation `P(s) P(1 − s) = 1`. -/
theorem blaschkePair_mul_one_sub (a : ℂ) {s : ℂ} (h1 : s ≠ a) (h2 : s ≠ conj a)
    (h3 : s ≠ 1 - a) (h4 : s ≠ 1 - conj a) :
    blaschkePair a s * blaschkePair a (1 - s) = 1 := by
  have e1 : s - a ≠ 0 := sub_ne_zero.mpr h1
  have e2 : s - conj a ≠ 0 := sub_ne_zero.mpr h2
  have e3 : s - (1 - a) ≠ 0 := sub_ne_zero.mpr h3
  have e4 : s - (1 - conj a) ≠ 0 := sub_ne_zero.mpr h4
  have f1 : 1 - s - (1 - conj a) ≠ 0 := by
    intro h; apply e2; linear_combination -h
  have f2 : 1 - s - (1 - conj (conj a)) ≠ 0 := by
    rw [Complex.conj_conj]; intro h; apply e1; linear_combination -h
  unfold blaschkePair halfBlaschke
  rw [Complex.conj_conj] at *
  field_simp
  ring

/-- The Blaschke pair is real on the real axis: `P(s̄) = P(s)^*`. -/
theorem blaschkePair_conj (a s : ℂ) : blaschkePair a (conj s) = conj (blaschkePair a s) := by
  unfold blaschkePair halfBlaschke
  simp only [map_mul, map_div₀, map_sub, map_one, Complex.conj_conj]
  ring

/-- **Schur positivity cannot place scattering zeros.** For any coefficient `φ` and any `a` with
`Re a > 1/2`, the coefficient `ψ = φ · P_a` has the same functional-equation product, the same
real symmetry, the same modulus on `Re s = 1/2`, modulus at most that of `φ` on `Re s ≥ 1/2`, a
Schur form at least that of `φ` on every node family in `Re s > 1/2`, and zeros at `a` and `ā`. -/
theorem scattering_positivity_blind_to_zeros (φ : ℂ → ℂ) {a : ℂ} (ha : 1 / 2 < a.re) :
    let ψ := fun z => φ z * blaschkePair a z
    (∀ s, s ≠ a → s ≠ conj a → s ≠ 1 - a → s ≠ 1 - conj a →
        ψ s * ψ (1 - s) = φ s * φ (1 - s)) ∧
      ((∀ s, φ (conj s) = conj (φ s)) → ∀ s, ψ (conj s) = conj (ψ s)) ∧
      (∀ s, s.re = 1 / 2 → ‖ψ s‖ = ‖φ s‖) ∧
      (∀ s, 1 / 2 ≤ s.re → ‖ψ s‖ ≤ ‖φ s‖) ∧
      (∀ {n : ℕ} (s c : Fin n → ℂ), (∀ i, 1 / 2 < (s i).re) →
        (schurForm φ s c).re ≤ (schurForm ψ s c).re) ∧
      ψ a = 0 ∧ ψ (conj a) = 0 := by
  intro ψ
  have ha' : 1 / 2 < (conj a).re := by rwa [Complex.conj_re]
  refine ⟨fun s h1 h2 h3 h4 => ?_, fun hφ s => ?_, fun s hs => ?_, fun s hs => ?_,
    fun s c hs => ?_, ?_, ?_⟩
  · have h := blaschkePair_mul_one_sub a h1 h2 h3 h4
    calc ψ s * ψ (1 - s) = φ s * φ (1 - s) * (blaschkePair a s * blaschkePair a (1 - s)) := by
          simp only [ψ]; ring
      _ = φ s * φ (1 - s) := by rw [h, mul_one]
  · simp only [ψ, hφ, blaschkePair_conj, map_mul]
  · simp only [ψ, blaschkePair, norm_mul, norm_halfBlaschke_of_re_eq_half ha hs,
      norm_halfBlaschke_of_re_eq_half ha' hs, mul_one]
  · simp only [ψ, blaschkePair, norm_mul]
    have h1 := norm_halfBlaschke_le_one ha hs
    have h2 := norm_halfBlaschke_le_one ha' hs
    calc ‖φ s‖ * (‖halfBlaschke a s‖ * ‖halfBlaschke (conj a) s‖) ≤ ‖φ s‖ * (1 * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one)
            (norm_nonneg _)
      _ = ‖φ s‖ := by ring
  · have step1 := re_schurForm_le_mul_halfBlaschke φ s c ha hs
    have step2 := re_schurForm_le_mul_halfBlaschke (fun z => φ z * halfBlaschke a z) s c ha' hs
    have e : (fun z => (φ z * halfBlaschke a z) * halfBlaschke (conj a) z) = ψ := by
      funext z; simp only [ψ, blaschkePair]; ring
    rw [e] at step2
    exact step1.trans step2
  · simp [ψ, blaschkePair, halfBlaschke]
  · simp [ψ, blaschkePair, halfBlaschke]

end

end GaloisForLFunctions.RenormalizedIntersectionTheory
