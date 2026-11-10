import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheSignIsCarriedByTheContacts
import GaloisForLFunctions.RHTower.WeilPositivityImaginaryQuadraticConductorLaw
import GaloisForLFunctions.RHTower.BlindSymbolSlackPrimePowerPeriodization
import GaloisForLFunctions.RHTower.WeilPoleWeightAtMostOne
import GaloisForLFunctions.RHTower.CHMDHalfTimeSecantAutocorrelationAndPolarAntiNodeTests

/-!
# The square of a quadratic ring pairs on the comb of the integers with its conductor

Let `χ` be a real primitive character of conductor `q > 1`, the character of a quadratic field
`K` of discriminant `±q`. The ideals of the ring of integers of `K` are the degree points of its
square; counted by their norms they sit on the comb of the integers, with the contacts
`Λ(n)(1 + χ(n))`: two prime ideals above a split prime, one of norm `p²` above an inert prime,
one above a ramified prime. The zeta function of `K` is `ζ(s) L(s, χ)`, and the pairing splits
into the pairing of `ℤ` and a part twisted by `χ`.

* **The explicit formula as a functional** (`re_weilFullFunctional_eq_pole_add_symbol`,
  `re_weilFullFunctional_twist`): on a test, the functional of the weight `Λχ` is the pole term
  plus the sum over the zeros of `L(s, χ)`, minus `log q` times the mass, minus the energy of the
  kernel `π/cosh(πτ)` when `χ` is odd.
* **The conjugate jets** (`integral_normSq_paperFT_mul_sech`, `placeEnergy_eq_conjugateForm`,
  `tendsto_conjugateJet`, `integral_window_conjugate`): that energy is the pairing of the
  autocorrelation with `1/(2 cosh(x/2))`,
  the difference of the Lévy densities of `Γ_ℝ(s)` and `Γ_ℝ(s + 1)`, and on the degree points it
  is the limit of the jets `1/(m + n)`.
* **The twisted part** (`tendsto_twistedForm_add_twistedContact`): jets, the counterterm
  `log(qn/2π)` and twice the contacts `Λχ` tend to minus the sum over the zeros of `L(s, χ)`.
  There is no pole plane, and the conductor enters as a density: the counterterm is that of a
  comb `q` times as dense as the integers.
* **The ring** (`tendsto_quadraticForm_add_idealContact`): jets of both archimedean factors, the
  counterterm `log(q n²/(2π)²)` and twice the contacts of the ideals tend to
  `2 d₁ d₂ − Z_ζ(f) − Z_χ(f)`: twice the product of the degrees minus the sum over the zeros of
  the zeta function of `K`.
* **The shape** (`two_mul_levyKernel_sub_conjugate`, `quadraticForm_eq`): for an imaginary
  quadratic ring the jets between the norms `m ≠ n` are `1/|m − n|`, the trace of the weights
  `0, 1, 2, …` of the complex place; the mass at `n` enters with `log(q n²/(2π)²)`.

So the discriminant of a quadratic ring is not an invariant of a point of its square: it is the
density of the comb on which the twisted part of the pairing lives. The class group does not
enter the pairing of the degree points counted by their norms: contacts, jets and counterterm
depend on `χ` alone.
-/

open Finset Filter Topology MeasureTheory
open Zeta23
open scoped ArithmeticFunction.vonMangoldt Real

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### The functional of a weight in symbol form -/

/-- **The functional of a weight on a test is its pole term plus its symbol energy.** For a test
`F` supported in `[−a, a]`, `Re W_λ(F ⋆ F̃) = Re pole + (1/2π) ∫ |F̂|² S_λ`. -/
theorem re_weilFullFunctional_eq_pole_add_symbol (lam : ℕ → ℝ) {a : ℝ} {F : ℝ → ℂ}
    (hF : ContDiff ℝ 2 F) (hFs : tsupport F ⊆ Set.Icc (-a) a) :
    (_root_.RHTower.weilFullFunctional lam (EF.weilTest F F)).re =
      (_root_.RHTower.weilPoleTerm (EF.weilTest F F)).re +
        1 / (2 * π) * ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 *
          _root_.RHTower.weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) := by
  obtain ⟨hFc, -, hks, -, -⟩ := _root_.RHTower.weilTest_self_data hF hFs
  have hout : ∀ y : ℝ, 2 * a < |y| → EF.weilTest F F y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun hmem => by
      have h := hks hmem
      have : |y| ≤ 2 * a := abs_le.mpr ⟨h.1, h.2⟩
      linarith
  have hvan : ∀ n : ℕ, ⌊Real.exp (2 * a)⌋₊ < n →
      EF.weilTest F F (Real.log n) = 0 ∧ EF.weilTest F F (-Real.log n) = 0 := by
    intro n hn
    have hexp : Real.exp (2 * a) < n := (Nat.floor_lt (Real.exp_pos _).le).mp hn
    have hlog : 2 * a < Real.log n := by
      rw [← Real.log_exp (2 * a)]
      exact Real.log_lt_log (Real.exp_pos _) hexp
    have hl0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    exact ⟨hout _ (by rwa [abs_of_nonneg hl0]), hout _ (by rwa [abs_neg, abs_of_nonneg hl0])⟩
  have hsum : (∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
        (EF.weilTest F F (Real.log n) + EF.weilTest F F (-Real.log n))).re =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, lam n / Real.sqrt n *
        (EF.weilTest F F (Real.log n) + EF.weilTest F F (-Real.log n)).re := by
    rw [tsum_eq_sum (s := Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊) (fun n hn => ?_), Complex.re_sum]
    · refine Finset.sum_congr rfl fun n hn => ?_
      rw [if_pos (Finset.mem_Icc.mp hn).1, Complex.re_ofReal_mul]
    · rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
      rcases hn with h | h
      · rw [if_neg (by omega), Complex.ofReal_zero, zero_mul]
      · rw [(hvan n h).1, (hvan n h).2, add_zero, mul_zero]
  have h0 : _root_.RHTower.WeilOneSided.weilArchRe (EF.weilTest F F) -
        (_root_.RHTower.weilPoleTerm (EF.weilTest F F)).re =
      1 / (2 * π) * ∫ r : ℝ, ‖paperFT F r‖ ^ 2 * EF.gammaBracket r :=
    _root_.RHTower.BlindPrimePowerSlack.weilArchRe_sub_pole_eq ⟨F, hF, hFc⟩
  have hgam : ∫ r : ℝ, ‖paperFT F r‖ ^ 2 * EF.gammaBracket r =
      ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 * _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) :=
    integral_congr_ae (Eventually.of_forall fun r => by
      show ‖paperFT F r‖ ^ 2 * EF.gammaBracket r = _
      rw [_root_.RHTower.WeilPoleWeight.gammaBracket_eq_archimedeanWeilSymbol])
  rw [hgam] at h0
  have hfull : (_root_.RHTower.weilFullFunctional lam (EF.weilTest F F)).re =
      _root_.RHTower.WeilOneSided.weilArchRe (EF.weilTest F F) -
        (∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
          (EF.weilTest F F (Real.log n) + EF.weilTest F F (-Real.log n))).re := by
    unfold _root_.RHTower.weilFullFunctional _root_.RHTower.WeilOneSided.weilArchRe
    simp only [Complex.add_re, Complex.sub_re]
    ring
  rw [hfull, hsum, _root_.RHTower.integral_weilAtomSymbol_eq_arch_sub hF hFs lam, mul_sub, ← h0]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-! ### The contacts of a quadratic ring -/

variable {q : ℕ}

/-- The contacts twisted by a real character: `Λ(n) χ(n)`. -/
def twistWeight (χ : DirichletCharacter ℂ q) (n : ℕ) : ℝ := Λ n * (χ (n : ZMod q)).re

/-- The contacts of the ideals of the quadratic ring of `χ`, counted by their norms:
`Λ(n)(1 + χ(n))`. At a split prime `p` two prime ideals of norm `p` give `2 log p` at every power
of `p`; at an inert prime the ideal of norm `p²` gives `2 log p` at the even powers; at a ramified
prime one ideal of norm `p` gives `log p` at every power. -/
def idealWeight (χ : DirichletCharacter ℂ q) (n : ℕ) : ℝ := Λ n * (1 + (χ (n : ZMod q)).re)

theorem idealWeight_eq (χ : DirichletCharacter ℂ q) (n : ℕ) :
    idealWeight χ n = Λ n + twistWeight χ n := by
  unfold idealWeight twistWeight
  ring

open Classical in
/-- The energy of the kernel `π/cosh(πτ)` on a test. It enters for an odd character, whose second
archimedean factor is `Γ_ℝ(s + 1)` in place of `Γ_ℝ(s)`. -/
def placeEnergy (χ : DirichletCharacter ℂ q) (F : ℝ → ℂ) : ℝ :=
  if χ.Even then 0
  else 1 / (2 * π) * ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 * (π / Real.cosh (π * τ))

theorem placeEnergy_of_even {χ : DirichletCharacter ℂ q} (h : χ.Even) (F : ℝ → ℂ) :
    placeEnergy χ F = 0 :=
  if_pos h

theorem not_even_of_odd {χ : DirichletCharacter ℂ q} (h : χ.Odd) : ¬ χ.Even := fun he => by
  have h1 : χ (-1) = 1 := he
  have h2 : χ (-1) = -1 := h
  rw [h1] at h2
  norm_num at h2

theorem placeEnergy_of_odd {χ : DirichletCharacter ℂ q} (h : χ.Odd) (F : ℝ → ℂ) :
    placeEnergy χ F =
      1 / (2 * π) * ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 * (π / Real.cosh (π * τ)) :=
  if_neg (not_even_of_odd h)

theorem placeEnergy_nonneg (χ : DirichletCharacter ℂ q) (F : ℝ → ℂ) : 0 ≤ placeEnergy χ F := by
  unfold placeEnergy
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (by positivity) (integral_nonneg fun τ =>
      mul_nonneg (sq_nonneg _) (div_nonneg Real.pi_pos.le (Real.cosh_pos _).le))

/-- **The explicit formula of `L(s, χ)` as the functional of the twisted contacts.** For a real
primitive character `χ` of conductor `q > 1` and a test `F` supported in `[−a, a]`, the
functional of the weight `Λχ` is the pole term plus the sum over the zeros of `L(s, χ)`, minus
`log q` times the mass, minus the energy of the second archimedean factor. -/
theorem re_weilFullFunctional_twist [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0) {a : ℝ} (ha : 0 ≤ a)
    {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F) (hFs : tsupport F ⊆ Set.Icc (-a) a) :
    (_root_.RHTower.weilFullFunctional (twistWeight χ) (EF.weilTest F F)).re =
      (_root_.RHTower.weilPoleTerm (EF.weilTest F F)).re +
        ((_root_.RHTower.dirichletZeros hq hprim).W F F).re -
        Real.log q * (∫ x, ‖F x‖ ^ 2) - placeEnergy χ F := by
  rw [re_weilFullFunctional_eq_pole_add_symbol (twistWeight χ) hF hFs]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hpl := _root_.RHTower.integral_norm_paperFT_sq hF hFs
  rcases χ.even_or_odd with heven | hodd
  · have hsym : ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 * _root_.RHTower.weilAtomSymbol (twistWeight χ)
          ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) =
        2 * π * ((_root_.RHTower.dirichletZeros hq hprim).W F F).re -
          Real.log q * ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 :=
      _root_.RHTower.integral_weilAtomSymbol_dirichlet hq hprim heven hreal ha hF hFs
    rw [hsym, hpl, placeEnergy_of_even heven]
    field_simp
    ring
  · have hsym : ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 * _root_.RHTower.weilAtomSymbol (twistWeight χ)
          ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) =
        2 * π * ((_root_.RHTower.dirichletZeros hq hprim).W F F).re -
          Real.log q * (∫ τ : ℝ, ‖paperFT F τ‖ ^ 2) -
          ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 * (π / Real.cosh (π * τ)) :=
      _root_.RHTower.integral_weilAtomSymbol_dirichlet_odd hq hprim hodd hreal ha hF hFs
    rw [hsym, hpl, placeEnergy_of_odd hodd]
    field_simp
    ring

/-! ### Packets -/

variable {f : ℝ → ℝ}

/-- The sum over the zeros of `L(s, χ)` of a packet. -/
def twistedZeroSum [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive)
    (f : ℝ → ℝ) : ℝ :=
  ((_root_.RHTower.dirichletZeros hq hprim).W (fun u => (f u : ℂ)) (fun u => (f u : ℂ))).re

theorem exists_tsupport_ofReal_subset (hfc : HasCompactSupport f) :
    ∃ a : ℝ, 0 ≤ a ∧ tsupport (fun u => (f u : ℂ)) ⊆ Set.Icc (-a) a := by
  obtain ⟨A, hA⟩ := (hasCompactSupport_ofReal_packet hfc).isCompact.isBounded.subset_closedBall 0
  refine ⟨|A|, abs_nonneg A, fun x hx => ?_⟩
  have := hA hx
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  exact abs_le.mp (this.trans (le_abs_self A))

theorem integral_norm_ofReal_sq (f : ℝ → ℝ) : ∫ x, ‖((f x : ℝ) : ℂ)‖ ^ 2 = ∫ x, f x ^ 2 :=
  integral_congr_ae (Eventually.of_forall fun x => by
    show ‖((f x : ℝ) : ℂ)‖ ^ 2 = f x ^ 2
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs])

/-- The explicit formula of `L(s, χ)` on a packet. -/
theorem re_weilFullFunctional_twist_packet [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    (_root_.RHTower.weilFullFunctional (twistWeight χ)
        (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re =
      2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) +
        twistedZeroSum hq hprim f - Real.log q * (∫ u, f u ^ 2) -
        placeEnergy χ (fun u => (f u : ℂ)) := by
  obtain ⟨a, ha, hfs⟩ := exists_tsupport_ofReal_subset hfc
  rw [re_weilFullFunctional_twist hq hprim hreal ha (contDiff_ofReal_packet hf) hfs,
    weilPoleTerm_packet hf.continuous hfc, integral_norm_ofReal_sq]
  rfl

/-! ### The jets of the conjugate factor -/

/-- The pairing of a packet with the kernel `1/(2 cosh(x/2))`, the difference of the Lévy
densities of `Γ_ℝ(s)` and `Γ_ℝ(s + 1)`. -/
def conjugateForm (f : ℝ → ℝ) : ℝ := ∫ x, packetAutocorr f x / (2 * Real.cosh (x / 2))

/-- **The energy of the kernel `π/cosh(πτ)` on a test.** The kernel is the cosine transform of
`1/(2 cosh(r/2))`, so the energy is the pairing of the autocorrelation with that function. -/
theorem integral_normSq_paperFT_mul_sech {a : ℝ} {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F)
    (hFs : tsupport F ⊆ Set.Icc (-a) a) :
    1 / (2 * π) * ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 * (π / Real.cosh (π * τ)) =
      1 / 4 * ∫ r : ℝ, (Real.cosh (r / 2))⁻¹ *
        (EF.weilTest F F r + EF.weilTest F F (-r)).re := by
  obtain ⟨hFc, -, -, -, -⟩ := _root_.RHTower.weilTest_self_data hF hFs
  have hh : Integrable fun τ : ℝ => ‖paperFT F τ‖ ^ 2 :=
    _root_.RHTower.integrable_normSq_paperFT hF hFs
  have hhc : Continuous fun τ : ℝ => ‖paperFT F τ‖ ^ 2 :=
    _root_.RHTower.BlindPrimePowerSlack.continuous_normSq_paperFT ⟨F, hF, hFc⟩
  have hκ := _root_.RHTower.CHMDHalfTime.integrable_inv_cosh_half
  have hκc := _root_.RHTower.CHMDHalfTime.continuous_inv_cosh_half
  -- the kernel `π/cosh(πτ)` is the cosine transform of `1/(2 cosh(r/2))`
  have hpair : ∀ τ : ℝ, π / Real.cosh (π * τ) =
      1 / 2 * ∫ r : ℝ, (Real.cosh (r / 2))⁻¹ * Real.cos (r * τ) := fun τ => by
    rw [_root_.RHTower.CHMDHalfTime.integral_inv_cosh_half_mul_cos,
      _root_.RHTower.CHMDHalfTime.sechPiProfile]
    ring
  -- the two integrations commute
  have hG : Integrable (Function.uncurry fun τ r : ℝ =>
      ‖paperFT F τ‖ ^ 2 * ((Real.cosh (r / 2))⁻¹ * Real.cos (r * τ)))
      (volume.prod volume) := by
    refine (hh.mul_prod hκ).mono' ?_ (Eventually.of_forall fun z => ?_)
    · exact ((hhc.comp continuous_fst).mul ((hκc.comp continuous_snd).mul
        (Real.continuous_cos.comp (continuous_snd.mul continuous_fst)))).aestronglyMeasurable
    · show ‖‖paperFT F z.1‖ ^ 2 * ((Real.cosh (z.2 / 2))⁻¹ * Real.cos (z.2 * z.1))‖ ≤
        ‖paperFT F z.1‖ ^ 2 * (Real.cosh (z.2 / 2))⁻¹
      have hc : 0 < (Real.cosh (z.2 / 2))⁻¹ := inv_pos.mpr (Real.cosh_pos _)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_pos hc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right hc.le (Real.abs_cos_le_one _)) (sq_nonneg _)
  have hswap := integral_integral_swap hG
  -- the cosine moments of `|F̂|²` are the autocorrelation
  have hinner : ∀ r : ℝ, ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 *
        ((Real.cosh (r / 2))⁻¹ * Real.cos (r * τ)) =
      π * ((Real.cosh (r / 2))⁻¹ * (EF.weilTest F F r + EF.weilTest F F (-r)).re) := fun r => by
    have h1 : ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 * ((Real.cosh (r / 2))⁻¹ * Real.cos (r * τ)) =
        (Real.cosh (r / 2))⁻¹ * ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 * Real.cos (τ * r) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun τ => by
        show ‖paperFT F τ‖ ^ 2 * ((Real.cosh (r / 2))⁻¹ * Real.cos (r * τ)) =
          (Real.cosh (r / 2))⁻¹ * (‖paperFT F τ‖ ^ 2 * Real.cos (τ * r))
        rw [mul_comm r τ]
        ring)
    rw [h1, _root_.RHTower.integral_normSq_paperFT_mul_cos_eq hF hFs r]
    ring
  have hL : ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 * (π / Real.cosh (π * τ)) =
      1 / 2 * ∫ τ : ℝ, ∫ r : ℝ, ‖paperFT F τ‖ ^ 2 *
        ((Real.cosh (r / 2))⁻¹ * Real.cos (r * τ)) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun τ => by
      show ‖paperFT F τ‖ ^ 2 * (π / Real.cosh (π * τ)) =
        1 / 2 * ∫ r : ℝ, ‖paperFT F τ‖ ^ 2 * ((Real.cosh (r / 2))⁻¹ * Real.cos (r * τ))
      rw [hpair τ, integral_const_mul]
      ring)
  rw [hL, hswap, integral_congr_ae (Eventually.of_forall hinner), integral_const_mul]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **On a packet the energy of the kernel `π/cosh(πτ)` is the pairing with `1/(2 cosh(x/2))`.** -/
theorem placeEnergy_eq_conjugateForm (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    1 / (2 * π) * ∫ τ : ℝ, ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 * (π / Real.cosh (π * τ)) =
      conjugateForm f := by
  obtain ⟨a, -, hFs⟩ := exists_tsupport_ofReal_subset hfc
  have hk : ∀ y : ℝ, EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) y =
      ((packetAutocorr f y : ℝ) : ℂ) := fun y => weilTest_packet f y
  rw [integral_normSq_paperFT_mul_sech (contDiff_ofReal_packet hf) hFs, conjugateForm,
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  show 1 / 4 * ((Real.cosh (r / 2))⁻¹ *
      (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) r +
        EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) (-r)).re) =
    packetAutocorr f r / (2 * Real.cosh (r / 2))
  rw [hk, hk, packetAutocorr_neg, ← Complex.ofReal_add, Complex.ofReal_re,
    show packetAutocorr f r / (2 * Real.cosh (r / 2)) =
      1 / 2 * (packetAutocorr f r * (Real.cosh (r / 2))⁻¹) by
        rw [div_eq_mul_inv, mul_inv]
        ring]
  ring

/-- The energy of the second archimedean factor does not change under a translation of the
packet. -/
theorem placeEnergy_translate (χ : DirichletCharacter ℂ q) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (s : ℝ) :
    placeEnergy χ (fun u => ((f (u - s) : ℝ) : ℂ)) = placeEnergy χ (fun u => (f u : ℂ)) := by
  have hg : ContDiff ℝ 2 fun u => f (u - s) := hf.comp (contDiff_id.sub contDiff_const)
  have hgc : HasCompactSupport fun u => f (u - s) :=
    hfc.comp_homeomorph (Homeomorph.subRight s)
  rcases χ.even_or_odd with heven | hodd
  · rw [placeEnergy_of_even heven, placeEnergy_of_even heven]
  · have e : 1 / (2 * π) * ∫ τ : ℝ, ‖paperFT (fun u => ((f (u - s) : ℝ) : ℂ)) τ‖ ^ 2 *
          (π / Real.cosh (π * τ)) = conjugateForm fun u => f (u - s) :=
      placeEnergy_eq_conjugateForm hg hgc
    rw [placeEnergy_of_odd hodd, placeEnergy_of_odd hodd, placeEnergy_eq_conjugateForm hf hfc, e]
    simp only [conjugateForm, packetAutocorr_translate]

/-- The sum over the zeros of `L(s, χ)` does not change under a translation of the packet. -/
theorem twistedZeroSum_translate [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (s : ℝ) :
    twistedZeroSum hq hprim (fun u => f (u - s)) = twistedZeroSum hq hprim f := by
  have hg : ContDiff ℝ 2 fun u => f (u - s) := hf.comp (contDiff_id.sub contDiff_const)
  have hgc : HasCompactSupport fun u => f (u - s) :=
    hfc.comp_homeomorph (Homeomorph.subRight s)
  obtain ⟨a, ha, hfs⟩ := exists_tsupport_ofReal_subset hfc
  obtain ⟨b, hb, hgs⟩ := exists_tsupport_ofReal_subset hgc
  have h1 := re_weilFullFunctional_twist hq hprim hreal ha (contDiff_ofReal_packet hf) hfs
  have h2 : (_root_.RHTower.weilFullFunctional (twistWeight χ)
        (EF.weilTest (fun u => ((f (u - s) : ℝ) : ℂ)) (fun u => ((f (u - s) : ℝ) : ℂ)))).re =
      (_root_.RHTower.weilPoleTerm
        (EF.weilTest (fun u => ((f (u - s) : ℝ) : ℂ)) (fun u => ((f (u - s) : ℝ) : ℂ)))).re +
        twistedZeroSum hq hprim (fun u => f (u - s)) -
        Real.log q * (∫ x, ‖((f (x - s) : ℝ) : ℂ)‖ ^ 2) -
        placeEnergy χ (fun u => ((f (u - s) : ℝ) : ℂ)) :=
    re_weilFullFunctional_twist hq hprim hreal hb (contDiff_ofReal_packet hg) hgs
  have hm : ∫ x, ‖((f (x - s) : ℝ) : ℂ)‖ ^ 2 = ∫ x, ‖((f x : ℝ) : ℂ)‖ ^ 2 :=
    integral_sub_right_eq_self (fun x => ‖((f x : ℝ) : ℂ)‖ ^ 2) s
  rw [weilTest_packet_translate f s, placeEnergy_translate χ hf hfc s, hm] at h2
  have h3 : twistedZeroSum hq hprim (fun u => f (u - s)) =
      ((_root_.RHTower.dirichletZeros hq hprim).W (fun u => (f u : ℂ))
        (fun u => (f u : ℂ))).re := by
    linarith
  exact h3

/-- The jets of the conjugate factor on the degree points of a window: `1/(m + n)` in the unitary
normalization, with the diagonal. -/
def conjugateJet (f : ℝ → ℝ) (L N : ℕ) : ℝ :=
  ∑ m ∈ Ioc N (N + L * N), ∑ n ∈ Ioc N (N + L * N),
    degreeSample f N m * degreeSample f N n / (Real.sqrt m * Real.sqrt n * ((m : ℝ) + n))

/-- The jets of the conjugate factor on a packet are a Riemann sum. -/
theorem tendsto_conjugateJet (hcont : Continuous f) (L : ℕ) :
    Tendsto (conjugateJet f L) atTop
      (𝓝 (∫ u in (0 : ℝ)..Real.log (1 + L), ∫ v in (0 : ℝ)..Real.log (1 + L),
        f u * f v / (2 * Real.cosh ((u - v) / 2)))) := by
  have hΨ : Continuous (Function.uncurry fun u v : ℝ =>
      f u * f v / (2 * Real.cosh ((u - v) / 2))) :=
    ((hcont.comp continuous_fst).mul (hcont.comp continuous_snd)).div
      (continuous_const.mul
        (Real.continuous_cosh.comp ((continuous_fst.sub continuous_snd).div_const 2)))
      fun p => (mul_pos two_pos (Real.cosh_pos _)).ne'
  refine (tendsto_degreePairSum hΨ L).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold conjugateJet
  refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun n hn => ?_
  have hm' : (0 : ℝ) < m := by
    have := (Finset.mem_Ioc.mp hm).1
    exact_mod_cast (by omega : 0 < m)
  have hn' : (0 : ℝ) < n := by
    have := (Finset.mem_Ioc.mp hn).1
    exact_mod_cast (by omega : 0 < n)
  obtain ⟨s, hs, hms⟩ : ∃ s : ℝ, 0 < s ∧ (m : ℝ) = s ^ 2 :=
    ⟨_, Real.sqrt_pos.mpr hm', (Real.sq_sqrt hm'.le).symm⟩
  obtain ⟨t, ht, hnt⟩ : ∃ t : ℝ, 0 < t ∧ (n : ℝ) = t ^ 2 :=
    ⟨_, Real.sqrt_pos.mpr hn', (Real.sq_sqrt hn'.le).symm⟩
  have hlog : Real.log ((m : ℝ) / N) - Real.log ((n : ℝ) / N) = Real.log ((m : ℝ) / n) := by
    rw [Real.log_div hm'.ne' hN'.ne', Real.log_div hn'.ne' hN'.ne',
      Real.log_div hm'.ne' hn'.ne']
    ring
  have hcosh : 2 * Real.cosh (Real.log ((m : ℝ) / n) / 2) = (s ^ 2 + t ^ 2) / (s * t) := by
    have hst : Real.sqrt ((m : ℝ) / n) = s / t := by
      rw [hms, hnt, ← div_pow, Real.sqrt_sq (div_pos hs ht).le]
    rw [← Real.log_sqrt (div_pos hm' hn').le, hst, Real.cosh_log (div_pos hs ht)]
    field_simp
  show f (Real.log ((m : ℝ) / N)) * f (Real.log ((n : ℝ) / N)) /
        (2 * Real.cosh ((Real.log ((m : ℝ) / N) - Real.log ((n : ℝ) / N)) / 2)) / ((m : ℝ) * n) =
      degreeSample f N m * degreeSample f N n / (Real.sqrt m * Real.sqrt n * ((m : ℝ) + n))
  rw [hlog, hcosh, degreeSample, degreeSample, hms, hnt, Real.sqrt_sq hs.le, Real.sqrt_sq ht.le]
  field_simp

/-- **On a packet in a window the pairing with `1/(2 cosh)` over the window is the pairing of the
autocorrelation.** -/
theorem integral_window_conjugate (hcont : Continuous f) (hfc : HasCompactSupport f) {δ c : ℝ}
    (hδ : 0 < δ) (hsupp : ∀ u, u ≤ δ ∨ c - δ ≤ u → f u = 0) :
    (∫ u in (0 : ℝ)..c, ∫ v in (0 : ℝ)..c, f u * f v / (2 * Real.cosh ((u - v) / 2))) =
      conjugateForm f := by
  have hwin : ∀ {u : ℝ}, f u ≠ 0 → u ∈ Set.Ioc (0 : ℝ) c := fun {u} hu => by
    obtain ⟨h1, h2⟩ := ne_zero_imp_mem_window hsupp hu
    exact ⟨by linarith, by linarith⟩
  -- the inner integral over the window is an integral over the line, in the variable `v − u`
  have hinner : ∀ u : ℝ, (∫ v in (0 : ℝ)..c, f u * f v / (2 * Real.cosh ((u - v) / 2))) =
      ∫ x, f u * f (u + x) / (2 * Real.cosh (x / 2)) := fun u => by
    rw [intervalIntegral.integral_eq_integral_of_support_subset (fun v hv => hwin fun h0 => hv (by
      show f u * f v / (2 * Real.cosh ((u - v) / 2)) = 0
      rw [h0, mul_zero, zero_div])),
      ← integral_add_left_eq_self (fun v => f u * f v / (2 * Real.cosh ((u - v) / 2))) u]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show f u * f (u + x) / (2 * Real.cosh ((u - (u + x)) / 2)) =
      f u * f (u + x) / (2 * Real.cosh (x / 2))
    rw [show (u - (u + x)) / 2 = -(x / 2) by ring, Real.cosh_neg]
  rw [intervalIntegral.integral_congr fun u _ => hinner u,
    intervalIntegral.integral_eq_integral_of_support_subset (fun u hu => hwin fun h0 => hu (by
      show ∫ x, f u * f (u + x) / (2 * Real.cosh (x / 2)) = 0
      simp [h0]))]
  -- the two integrations commute
  obtain ⟨B, hB⟩ := hfc.exists_bound_of_continuous hcont
  have hfi : Integrable f := hcont.integrable_of_hasCompactSupport hfc
  have hκ := _root_.RHTower.CHMDHalfTime.integrable_inv_cosh_half
  have hκc := _root_.RHTower.CHMDHalfTime.continuous_inv_cosh_half
  have hG : Integrable (Function.uncurry fun u x : ℝ =>
      f u * f (u + x) / (2 * Real.cosh (x / 2))) (volume.prod volume) := by
    refine ((hfi.norm.const_mul B).mul_prod hκ).mono' ?_ (Eventually.of_forall fun z => ?_)
    · exact (((hcont.comp continuous_fst).mul (hcont.comp (continuous_fst.add continuous_snd))).div
        (continuous_const.mul (Real.continuous_cosh.comp (continuous_snd.div_const 2)))
        fun p => (mul_pos two_pos (Real.cosh_pos _)).ne').aestronglyMeasurable
    · show ‖f z.1 * f (z.1 + z.2) / (2 * Real.cosh (z.2 / 2))‖ ≤
        B * ‖f z.1‖ * (Real.cosh (z.2 / 2))⁻¹
      have hc : 0 < Real.cosh (z.2 / 2) := Real.cosh_pos _
      have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB z.1)
      rw [norm_div, norm_mul, Real.norm_eq_abs (2 * Real.cosh (z.2 / 2)),
        abs_of_pos (mul_pos two_pos hc), div_eq_mul_inv, mul_inv]
      have h1 : ‖f z.1‖ * ‖f (z.1 + z.2)‖ ≤ B * ‖f z.1‖ := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
      have h2 : (2 : ℝ)⁻¹ * (Real.cosh (z.2 / 2))⁻¹ ≤ (Real.cosh (z.2 / 2))⁻¹ := by
        have := inv_pos.mpr hc
        linarith
      exact mul_le_mul h1 h2 (by positivity) (mul_nonneg hB0 (norm_nonneg _))
  rw [integral_integral_swap hG, conjugateForm]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show ∫ u, f u * f (u + x) / (2 * Real.cosh (x / 2)) =
    packetAutocorr f x / (2 * Real.cosh (x / 2))
  rw [packetAutocorr, ← integral_div]

/-! ### The pairing of the square of a quadratic ring -/

theorem weightedContact_idealWeight (χ : DirichletCharacter ℂ q) (f : ℝ → ℝ) (L N : ℕ) :
    weightedContact (idealWeight χ) f L N =
      degreeContact f L N + weightedContact (twistWeight χ) f L N := by
  rw [← weightedContact_vonMangoldt]
  unfold weightedContact
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [idealWeight_eq]
  ring

/-- The masses of a packet on the degree points of a window are a Riemann sum of `∫ f²`. -/
theorem tendsto_degreeMass (hcont : Continuous f) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => ∑ n ∈ Ioc N (N + 3 * K * N), degreeSample f N n ^ 2 / n) atTop
      (𝓝 (∫ u, f u ^ 2)) := by
  have hδ : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hsuppW := window_of_support hK hsupp
  have h := tendsto_degreeSum (G := fun u => f u ^ 2) (hcont.pow 2) (L := 3 * K) (by omega)
  have e : ∫ u, f u ^ 2 = ∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)), f u ^ 2 := by
    rw [← packetAutocorr_zero_eq_integral_window hδ hsuppW, packetAutocorr]
    exact integral_congr_ae (Eventually.of_forall fun u => by
      show f u ^ 2 = f u * f (u + 0)
      rw [add_zero, sq])
  rw [e]
  exact h

open Classical in
/-- The jets of the second archimedean factor of `χ` against those of the first, on the window:
absent for an even character, `1/(m + n)` for an odd one. -/
def placeJet (χ : DirichletCharacter ℂ q) (f : ℝ → ℝ) (L N : ℕ) : ℝ :=
  if χ.Even then 0 else conjugateJet f L N

theorem placeJet_of_even {χ : DirichletCharacter ℂ q} (h : χ.Even) (f : ℝ → ℝ) (L N : ℕ) :
    placeJet χ f L N = 0 :=
  if_pos h

theorem placeJet_of_odd {χ : DirichletCharacter ℂ q} (h : χ.Odd) (f : ℝ → ℝ) (L N : ℕ) :
    placeJet χ f L N = conjugateJet f L N :=
  if_neg (not_even_of_odd h)

/-- The conjugate jets of a packet tend to the energy of the second archimedean factor. -/
theorem tendsto_placeJet (χ : DirichletCharacter ℂ q) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    Tendsto (placeJet χ f (3 * K)) atTop (𝓝 (placeEnergy χ fun u => (f u : ℂ))) := by
  have hδ : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hsuppW := window_of_support hK hsupp
  rcases χ.even_or_odd with heven | hodd
  · rw [show placeJet χ f (3 * K) = fun _ => 0 from funext fun N => placeJet_of_even heven f _ N,
      placeEnergy_of_even heven]
    exact tendsto_const_nhds
  · rw [show placeJet χ f (3 * K) = conjugateJet f (3 * K) from
        funext fun N => placeJet_of_odd hodd f _ N,
      placeEnergy_of_odd hodd, placeEnergy_eq_conjugateForm hf hfc,
      ← integral_window_conjugate hf.continuous hfc hδ hsuppW]
    exact tendsto_conjugateJet hf.continuous (3 * K)

/-- The jets and the counterterm of the part of the pairing twisted by `χ`: the jets of the comb
of the integers, corrected by the conjugate jets for an odd character, and the counterterm
`log(qn/2π)` in place of `log(n/2π)`. -/
def twistedForm (χ : DirichletCharacter ℂ q) (f : ℝ → ℝ) (L N : ℕ) : ℝ :=
  degreeForm f L N - placeJet χ f L N -
    Real.log q * ∑ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n

/-- **The twisted part of the pairing weighs the zeros of `L(s, χ)` and has no pole plane.** For a
real primitive character of conductor `q > 1` and a packet in a window: jets, the counterterm
`log(qn/2π)` and twice the contacts of weight `Λχ` tend to minus the sum over the zeros of
`L(s, χ)`. -/
theorem tendsto_twistedForm_add_twistedContact [NeZero q] (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => twistedForm χ f (3 * K) N +
        2 * weightedContact (twistWeight χ) f (3 * K) N) atTop
      (𝓝 (-twistedZeroSum hq hprim f)) := by
  have h1 := tendsto_degreeForm_add_weightedContact (twistWeight χ) hf hfc hK hsupp
  rw [re_weilFullFunctional_twist_packet hq hprim hreal hf hfc] at h1
  have h2 := (tendsto_degreeMass hf.continuous hK hsupp).const_mul (Real.log q)
  have h := (h1.sub (tendsto_placeJet χ hf hfc hK hsupp)).sub h2
  have elim : 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
        (2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) +
          twistedZeroSum hq hprim f - Real.log q * (∫ u, f u ^ 2) -
          placeEnergy χ (fun u => (f u : ℂ))) -
        placeEnergy χ (fun u => (f u : ℂ)) - Real.log q * (∫ u, f u ^ 2) =
      -twistedZeroSum hq hprim f := by
    ring
  rw [elim] at h
  refine h.congr fun N => ?_
  unfold twistedForm
  ring

/-- The pairing of the degree points of the quadratic ring of `χ`, counted by their norms: the
jets of both archimedean factors and the counterterm `log(q n²/(2π)²)`. -/
def quadraticForm (χ : DirichletCharacter ℂ q) (f : ℝ → ℝ) (L N : ℕ) : ℝ :=
  degreeForm f L N + twistedForm χ f L N

/-- **The pairing of the square of a quadratic ring is twice the product of the degrees minus the
sum over the zeros of its zeta function.** Jets of both archimedean factors, the counterterm
`log(q n²/(2π)²)` and twice the contacts of the ideals tend to `2 d₁ d₂ − Z_ζ(f) − Z_χ(f)`. -/
theorem tendsto_quadraticForm_add_idealContact [NeZero q] (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => quadraticForm χ f (3 * K) N +
        2 * weightedContact (idealWeight χ) f (3 * K) N) atTop
      (𝓝 (2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
        (zeroSum f + twistedZeroSum hq hprim f))) := by
  have h := (tendsto_degreePairing_degrees_sub_zeroSum hf hfc hK hsupp).add
    (tendsto_twistedForm_add_twistedContact hq hprim hreal hf hfc hK hsupp)
  rw [show 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) - zeroSum f +
        -twistedZeroSum hq hprim f =
      2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
        (zeroSum f + twistedZeroSum hq hprim f) by ring] at h
  refine h.congr fun N => ?_
  rw [quadraticForm, weightedContact_idealWeight]
  ring

/-! ### The shape of the pairing -/

/-- **The jets of a complex place.** Twice the jets of the integers minus the conjugate jet is
`1/|m − n|` in the unitary normalization: the trace of the weights `0, 1, 2, …` of `Γ_ℂ`. -/
theorem two_mul_levyKernel_sub_conjugate {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    2 * levyKernel m n - 1 / (Real.sqrt m * Real.sqrt n * ((m : ℝ) + n)) =
      1 / (Real.sqrt m * Real.sqrt n * |(m : ℝ) - n|) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have habs : 0 < |(m : ℝ) - n| := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hmn))
  have hsm := Real.sqrt_pos.mpr hm'
  have hsn := Real.sqrt_pos.mpr hn'
  rw [levyKernel, jetKernel, Real.sqrt_mul hm'.le]
  field_simp
  ring

/-- **The counterterm of a quadratic ring carries the conductor.** The mass at `n` enters the
pairing with `log(q n²/(2π)²)`. -/
theorem quadraticForm_eq (hq : 0 < q) (χ : DirichletCharacter ℂ q) (f : ℝ → ℝ) (L N : ℕ) :
    quadraticForm χ f L N = 2 * degreePairing f L N - placeJet χ f L N -
      ∑ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n *
        Real.log ((q : ℝ) * (n : ℝ) ^ 2 / (2 * π) ^ 2) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hct : ∑ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n *
        Real.log ((q : ℝ) * (n : ℝ) ^ 2 / (2 * π) ^ 2) =
      2 * ∑ n ∈ Ioc N (N + L * N),
          degreeSample f N n ^ 2 / n * Real.log ((n : ℝ) / (2 * π)) +
        Real.log q * ∑ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : (0 : ℝ) < n := by
      have := (Finset.mem_Ioc.mp hn).1
      exact_mod_cast (by omega : 0 < n)
    have hlog : Real.log ((q : ℝ) * (n : ℝ) ^ 2 / (2 * π) ^ 2) =
        Real.log q + 2 * Real.log ((n : ℝ) / (2 * π)) := by
      rw [show (q : ℝ) * (n : ℝ) ^ 2 / (2 * π) ^ 2 = q * ((n : ℝ) / (2 * π)) ^ 2 by
          field_simp,
        Real.log_mul hq'.ne' (by positivity), Real.log_pow]
      push_cast
      ring
    rw [hlog]
    ring
  rw [quadraticForm, twistedForm, degreeForm, hct]
  ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
