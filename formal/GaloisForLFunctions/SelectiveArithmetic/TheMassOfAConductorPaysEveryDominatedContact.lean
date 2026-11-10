import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheHodgeIndexOfTheSquareOfAQuadraticRing
import GaloisForLFunctions.BiScaleUncertainty.PrimeWindowCeilingPolarAsymptotics

/-!
# The mass of a conductor pays every dominated contact

A *system* is a family of contact weights `w(n)` at the points `± log n`, a conductor `q` and the
archimedean symbol `S_∞` of `ζ`, without pole plane. Its form on a test `F` supported in `[−a, a]`
is

`𝔚_{w,q}(F) = (1/2π) ∫ |F̂|² (S_∞ + log q) − Σ_{2 ≤ n ≤ e^{2a}} w(n) n^{−1/2} · 2 Re (F ⋆ F̃)(log n)`.

For a primitive character `χ` of conductor `q` and `w = Λ Re χ` it is the sum over the zeros of
`L(s, χ)`, up to a nonnegative energy when `χ` is odd (`twistedZeroSum_eq_systemForm`).

* **The Schur price of sizes** (`abs_contactForm_le_of_psi`). If `|w(n)| ≤ Λ(n)` and
  `ψ(x) ≤ Kx + B`, the contact form on tests supported in `[−a, a]` is at most
  `(K e^{a} + B + (1 + 2a)²) ∫ |F|²` in absolute value. The contact operator is dominated by the
  shifts of the primes, whose kernel is `e^{|u−v|/2}` on average, and the Schur test with the
  polar weight `cosh(u/2)` gives its top `e^{a}`. The pointwise bound of the symbol,
  `2 Σ_{n ≤ e^{2a}} Λ(n) n^{−1/2} ≈ 4e^{a}`, is four times larger.
* **The dominated box is feasible** (`systemForm_ge_of_dominated`, `feasible_of_dominated`):
  `𝔚_{w,q}(F) ≥ (log q − A₀ − K e^{a} − B − (1 + 2a)²) ∫ |F|²`, with
  `A₀ = γ + 3 log 2 + π/2 + log π` the depth of the archimedean symbol.
* **The trivial aperture of a conductor** (`twistedZeroSum_ge_of_psi`, `exists_twistedZeroSum_ge`,
  `exists_trivialAperture_margin`). For every primitive character of conductor `q`, real or not,
  the sum over the zeros of `L(s, χ)` is at least `(log q − (1 + ε) e^{a} − (1 + 2a)² − B_ε) ∫ f²`
  on packets of aperture `a`. For every `η > 0` and all large conductors it is at least
  `½ (1 − e^{−η/2}) log q ∫ f²` on every packet of aperture `a ≤ log log q − η`.

So the sign of the twisted part of the square of a quadratic ring is a theorem up to the aperture
`log log q − o(1)`, and there it holds for every system of contacts of the size of the primes: it
carries no information on the character.
-/

open Finset Filter Topology MeasureTheory Set
open Zeta23
open scoped ArithmeticFunction.vonMangoldt Real

noncomputable section

namespace GaloisForLFunctions.SelectiveArithmetic

open AbsoluteGeometryOfSpecZ BiScaleUncertainty

/-! ### Dominated weight systems -/

/-- A weight system whose contacts have at most the size of the primes: `|w(n)| ≤ Λ(n)`. -/
def Dominated (w : ℕ → ℝ) : Prop := ∀ n, |w n| ≤ Λ n

theorem dominated_vonMangoldt : Dominated fun n => Λ n := fun _ =>
  (abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg).le

theorem Dominated.neg {w : ℕ → ℝ} (h : Dominated w) : Dominated fun n => -w n := fun n => by
  rw [abs_neg]
  exact h n

/-- The contacts of a character are dominated. -/
theorem dominated_twistWeight {q : ℕ} (χ : DirichletCharacter ℂ q) : Dominated (twistWeight χ) :=
  fun n => by
    rw [twistWeight, abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
      ((Complex.abs_re_le_norm _).trans (DirichletCharacter.norm_le_one χ _))

/-! ### The contact form and its Schur bound -/

/-- The contact form of a weight system on a test `F`, over the points `2 ≤ n ≤ N`:
`Σ w(n) n^{−1/2} Re (k(log n) + k(−log n))` with `k = F ⋆ F̃`. -/
def contactForm (w : ℕ → ℝ) (F : ℝ → ℂ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N, w n / Real.sqrt n *
    (EF.weilTest F F (Real.log n) + EF.weilTest F F (-Real.log n)).re

/-- **The Schur bound for a dominated system.** If a weight `φ` on the window `(a, a + L)` is a
supersolution of the prime shifts with constant `C`, the contact form of every dominated system on
tests supported in the window is at most `C ∫ |F|²` in absolute value. -/
theorem abs_weighted_logSum_le_of_schur {F : ℝ → ℂ} (hFc : Continuous F)
    (hFs : HasCompactSupport F) {a L : ℝ} (hsupp : ∀ u, F u ≠ 0 → u ∈ Ioo a (a + L))
    {w : ℕ → ℝ} (hw : Dominated w) (N : ℕ) {φ : ℝ → ℝ} (hφm : Measurable φ) {m M : ℝ}
    (hm : 0 < m) (hlo : ∀ t, m ≤ φ t) (hhi : ∀ t, φ t ≤ M) {C : ℝ}
    (hS : ∀ t ∈ Ioo a (a + L), ∑ n ∈ Finset.Ico 2 N,
      (Λ n : ℝ) / Real.sqrt n *
        ((Ioo a (a + L)).indicator φ (t - Real.log n) +
          (Ioo a (a + L)).indicator φ (t + Real.log n)) ≤ C * φ t) :
    |∑ n ∈ Finset.Ico 2 N, w n / Real.sqrt n *
        (EF.weilTest F F (Real.log n) + EF.weilTest F F (-Real.log n)).re| ≤
      C * ∫ u, ‖F u‖ ^ 2 := by
  have hφpos : ∀ t, 0 < φ t := fun t => hm.trans_le (hlo t)
  set I := Ioo a (a + L)
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ → ℝ, G = fun s t => ‖F t‖ ^ 2 *
      (I.indicator φ (t - s) / φ t + I.indicator φ (t + s) / φ t) := ⟨_, rfl⟩
  have hSch : ∀ s, 2 * |(EF.weilTest F F s).re| ≤ ∫ t, G s t := fun s => by
    rw [hG]; exact two_mul_abs_re_weilTest_le hFc hFs hsupp hφm hm hlo hhi s
  have hI : ∀ s, Integrable (G s) := fun s => by
    rw [hG]; exact integrable_schurIntegrand hFc hFs measurableSet_Ioo hφm hm hlo hhi s
  have hneg : ∀ s, G (-s) = G s := fun s => by
    rw [hG]; funext t; simp only [sub_neg_eq_add, ← sub_eq_add_neg]; ring
  have hpair : ∀ s, |(EF.weilTest F F s).re| + |(EF.weilTest F F (-s)).re| ≤ ∫ t, G s t := by
    intro s
    have h1 := hSch s
    have h2 := hSch (-s)
    rw [hneg] at h2
    linarith
  have hΛ : ∀ n : ℕ, 0 ≤ (Λ n : ℝ) / Real.sqrt n := fun n =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  -- each contact is paid by the prime shift of the same lag
  have hterm : ∀ n ∈ Finset.Ico 2 N,
      |w n / Real.sqrt n *
          (EF.weilTest F F (Real.log n) + EF.weilTest F F (-Real.log n)).re| ≤
        (Λ n : ℝ) / Real.sqrt n * ∫ t, G (Real.log n) t := by
    intro n _
    rw [abs_mul, abs_div, abs_of_nonneg (Real.sqrt_nonneg _), Complex.add_re]
    exact mul_le_mul (div_le_div_of_nonneg_right (hw n) (Real.sqrt_nonneg _))
      ((abs_add_le _ _).trans (hpair _)) (abs_nonneg _) (hΛ n)
  have hcs : HasCompactSupport (fun t => ‖F t‖ ^ 2) :=
    hFs.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
  have hnorm : Integrable (fun t => ‖F t‖ ^ 2) :=
    (hFc.norm.pow 2).integrable_of_hasCompactSupport hcs
  calc |∑ n ∈ Finset.Ico 2 N, w n / Real.sqrt n *
          (EF.weilTest F F (Real.log n) + EF.weilTest F F (-Real.log n)).re|
      ≤ ∑ n ∈ Finset.Ico 2 N, (Λ n : ℝ) / Real.sqrt n * ∫ t, G (Real.log n) t :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = ∫ t, ∑ n ∈ Finset.Ico 2 N, (Λ n : ℝ) / Real.sqrt n * G (Real.log n) t := by
        rw [integral_finsetSum _ fun n _ => (hI _).const_mul _]
        exact Finset.sum_congr rfl fun n _ => (integral_const_mul _ _).symm
    _ ≤ ∫ t, C * ‖F t‖ ^ 2 := by
        refine integral_mono (integrable_finsetSum _ fun n _ => (hI _).const_mul _)
          (hnorm.const_mul _) fun t => ?_
        by_cases h0 : F t = 0
        · simp [hG, h0]
        have hS' := hS t (hsupp t h0)
        have e : ∑ n ∈ Finset.Ico 2 N, (Λ n : ℝ) / Real.sqrt n * G (Real.log n) t =
            ‖F t‖ ^ 2 / φ t * ∑ n ∈ Finset.Ico 2 N, (Λ n : ℝ) / Real.sqrt n *
              (I.indicator φ (t - Real.log n) + I.indicator φ (t + Real.log n)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [hG]; field_simp
        rw [e, div_mul_eq_mul_div, div_le_iff₀ (hφpos t)]
        calc ‖F t‖ ^ 2 * (∑ n ∈ Finset.Ico 2 N, (Λ n : ℝ) / Real.sqrt n *
              (I.indicator φ (t - Real.log n) + I.indicator φ (t + Real.log n)))
            ≤ ‖F t‖ ^ 2 * (C * φ t) := mul_le_mul_of_nonneg_left hS' (sq_nonneg _)
          _ = C * ‖F t‖ ^ 2 * φ t := by ring
    _ = C * ∫ u, ‖F u‖ ^ 2 := integral_const_mul _ _

/-- A continuous test with topological support in `[−a, a]` vanishes at the two ends. -/
theorem mem_Ioo_of_ne_zero {a : ℝ} {F : ℝ → ℂ} (hF : Continuous F)
    (hFs : tsupport F ⊆ Icc (-a) a) {u : ℝ} (hu : F u ≠ 0) : u ∈ Ioo (-a) (-a + 2 * a) := by
  have hopen : IsOpen {v | F v ≠ 0} := isOpen_ne_fun hF continuous_const
  have hsub : {v | F v ≠ 0} ⊆ Icc (-a) a := fun v hv => hFs (subset_tsupport _ hv)
  have h := (hopen.subset_interior_iff.mpr hsub) hu
  rw [interior_Icc] at h
  exact ⟨h.1, by linarith [h.2]⟩

/-- **The Schur price of sizes.** If `ψ(x) ≤ Kx + B`, the contact form of a dominated system on a
test supported in `[−a, a]` is at most `(K e^{a} + B + (1 + 2a)²) ∫ |F|²` in absolute value. -/
theorem abs_contactForm_le_of_psi {K B : ℝ}
    (hψ : ∀ x : ℝ, 0 ≤ x → Chebyshev.psi x ≤ K * x + B) {a : ℝ} (ha : 0 ≤ a) {F : ℝ → ℂ}
    (hF : Continuous F) (hFs : tsupport F ⊆ Icc (-a) a) {w : ℕ → ℝ} (hw : Dominated w) (N : ℕ) :
    |contactForm w F N| ≤ (K * Real.exp a + B + (1 + 2 * a) ^ 2) * ∫ u, ‖F u‖ ^ 2 := by
  have hFc : HasCompactSupport F :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hFs
  have h := abs_weighted_logSum_le_of_schur hF hFc (fun u hu => mem_Ioo_of_ne_zero hF hFs hu) hw
    (N + 1) (continuous_polarWeight (-a) (2 * a)).measurable (Real.exp_pos (-(2 * a) / 2))
    (polarWeight_pos_lower (by linarith)) (polarWeight_le (by linarith))
    fun t ht => polar_schur_le ht _ hψ
  have e : 2 * a / 2 = a := by ring
  rw [e] at h
  rwa [contactForm, ← Finset.Ico_add_one_right_eq_Icc]

/-! ### The archimedean symbol is bounded below -/

/-- The depth of the archimedean symbol of `ζ`: `A₀ = γ + 3 log 2 + π/2 + log π = log π − ψ(¼)`. -/
def archConstant : ℝ :=
  Real.eulerMascheroniConstant + 3 * Real.log 2 + π / 2 + Real.log π

/-- `S_∞ ≥ −A₀`: on a vertical line the real part of the digamma function is least on the real
axis. -/
theorem neg_archConstant_le_archimedeanWeilSymbol (τ : ℝ) :
    -archConstant ≤ _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) := by
  have hmin := _root_.RHTower.digamma_real_le_re_digamma_add_mul_I (a := 1 / 4) (by norm_num)
    (τ / 2)
  have h14 : (Complex.digamma (((1 / 4 : ℝ) : ℂ))).re =
      -Real.eulerMascheroniConstant - 3 * Real.log 2 - π / 2 := by
    rw [show (((1 / 4 : ℝ) : ℂ)) = (1 / 4 : ℂ) by push_cast; ring,
      _root_.RHTower.re_digamma_one_quarter]
  have e := _root_.RHTower.archimedeanWeilSymbol_div_two_pi τ
  unfold archConstant
  linarith

/-- The archimedean energy of a test is at least `−A₀` times its mass. -/
theorem integral_arch_ge {a : ℝ} {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F)
    (hFs : tsupport F ⊆ Icc (-a) a) :
    -archConstant * (2 * π * ∫ x, ‖F x‖ ^ 2) ≤
      ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 * _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) := by
  rw [← _root_.RHTower.integral_norm_paperFT_sq hF hFs, ← integral_const_mul]
  refine integral_mono ((_root_.RHTower.integrable_normSq_paperFT hF hFs).const_mul _)
    (_root_.RHTower.integrable_normSq_paperFT_mul_arch hF hFs) fun τ => ?_
  have h := neg_archConstant_le_archimedeanWeilSymbol τ
  show -archConstant * ‖paperFT F τ‖ ^ 2 ≤
    ‖paperFT F τ‖ ^ 2 * _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π))
  nlinarith [sq_nonneg ‖paperFT F τ‖]

/-! ### The form of a system -/

/-- The form of the system `(w, q)` at aperture `a`: the archimedean symbol of `ζ`, the
counterterm of a comb of density `q`, the contacts `w` up to `e^{2a}`, no pole plane. -/
def systemForm (w : ℕ → ℝ) (q a : ℝ) (F : ℝ → ℂ) : ℝ :=
  1 / (2 * π) * ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 *
    (_root_.RHTower.weilAtomSymbol w ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) + Real.log q)

/-- A weight system is feasible for the conductor `q` at aperture `a` if its form is nonnegative
on every test supported in `[−a, a]`. -/
def Feasible (q a : ℝ) (w : ℕ → ℝ) : Prop :=
  ∀ F : ℝ → ℂ, ContDiff ℝ 2 F → tsupport F ⊆ Icc (-a) a → 0 ≤ systemForm w q a F

/-- The form of a system: archimedean energy, the conductor times the mass, minus the contact
form. -/
theorem systemForm_eq {a : ℝ} {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F) (hFs : tsupport F ⊆ Icc (-a) a)
    (w : ℕ → ℝ) (q : ℝ) :
    systemForm w q a F =
      1 / (2 * π) * (∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 *
          _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π))) +
        Real.log q * (∫ x, ‖F x‖ ^ 2) - contactForm w F ⌊Real.exp (2 * a)⌋₊ := by
  have hS := _root_.RHTower.integrable_normSq_paperFT_mul_weilAtomSymbol_of hF hFs w
  have hB : Integrable fun τ : ℝ => Real.log q * ‖paperFT F τ‖ ^ 2 :=
    (_root_.RHTower.integrable_normSq_paperFT hF hFs).const_mul _
  have hsplit : ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 *
        (_root_.RHTower.weilAtomSymbol w ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) + Real.log q) =
      (∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 *
          _root_.RHTower.weilAtomSymbol w ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) +
        Real.log q * ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 := by
    rw [← integral_const_mul, ← integral_add hS hB]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    show ‖paperFT F τ‖ ^ 2 *
        (_root_.RHTower.weilAtomSymbol w ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) + Real.log q) =
      ‖paperFT F τ‖ ^ 2 * _root_.RHTower.weilAtomSymbol w ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) +
        Real.log q * ‖paperFT F τ‖ ^ 2
    ring
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [systemForm, hsplit, _root_.RHTower.integral_weilAtomSymbol_eq_arch_sub hF hFs w,
    _root_.RHTower.integral_norm_paperFT_sq hF hFs, contactForm]
  field_simp
  ring

/-- **The form of a dominated system is bounded below by the conductor.** If `ψ(x) ≤ Kx + B`, then
`𝔚_{w,q}(F) ≥ (log q − A₀ − K e^{a} − B − (1 + 2a)²) ∫ |F|²` on tests supported in `[−a, a]`. -/
theorem systemForm_ge_of_dominated {K B : ℝ}
    (hψ : ∀ x : ℝ, 0 ≤ x → Chebyshev.psi x ≤ K * x + B) {a : ℝ} (ha : 0 ≤ a) {F : ℝ → ℂ}
    (hF : ContDiff ℝ 2 F) (hFs : tsupport F ⊆ Icc (-a) a) {w : ℕ → ℝ} (hw : Dominated w)
    (q : ℝ) :
    (Real.log q - archConstant - K * Real.exp a - B - (1 + 2 * a) ^ 2) * ∫ x, ‖F x‖ ^ 2 ≤
      systemForm w q a F := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have h1 := mul_le_mul_of_nonneg_left (integral_arch_ge hF hFs)
    (by positivity : (0 : ℝ) ≤ 1 / (2 * π))
  have e : 1 / (2 * π) * (-archConstant * (2 * π * ∫ x, ‖F x‖ ^ 2)) =
      -archConstant * ∫ x, ‖F x‖ ^ 2 := by
    field_simp
  rw [e] at h1
  have h2 := (abs_le.mp (abs_contactForm_le_of_psi hψ ha hF.continuous hFs hw
    ⌊Real.exp (2 * a)⌋₊)).2
  rw [systemForm_eq hF hFs]
  linarith

/-- **The dominated box is feasible below the trivial aperture.** -/
theorem feasible_of_dominated {K B : ℝ} (hψ : ∀ x : ℝ, 0 ≤ x → Chebyshev.psi x ≤ K * x + B)
    {a : ℝ} (ha : 0 ≤ a) {q : ℝ}
    (hq : archConstant + K * Real.exp a + B + (1 + 2 * a) ^ 2 ≤ Real.log q) {w : ℕ → ℝ}
    (hw : Dominated w) : Feasible q a w := fun F hF hFs =>
  le_trans (mul_nonneg (by linarith) (integral_nonneg fun _ => sq_nonneg _))
    (systemForm_ge_of_dominated hψ ha hF hFs hw q)

/-! ### The twisted part of the square of a quadratic ring -/

variable {q : ℕ} {f : ℝ → ℝ}

/-- **The sum over the zeros of `L(s, χ)` is the form of the system `(Λ Re χ, q)`**, plus the
energy of the second archimedean factor when `χ` is odd. -/
theorem twistedZeroSum_eq_systemForm [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hf : ContDiff ℝ 2 f) {a : ℝ}
    (hfs : tsupport (fun u => (f u : ℂ)) ⊆ Icc (-a) a) :
    twistedZeroSum hq hprim f =
      systemForm (twistWeight χ) q a (fun u => (f u : ℂ)) +
        placeEnergy χ (fun u => (f u : ℂ)) := by
  have hF := contDiff_ofReal_packet hf
  have hS := _root_.RHTower.integrable_normSq_paperFT_mul_weilAtomSymbol_of hF hfs (twistWeight χ)
  have hB : Integrable fun τ : ℝ => Real.log q * ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 :=
    (_root_.RHTower.integrable_normSq_paperFT hF hfs).const_mul _
  have hsplit : ∫ τ : ℝ, ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 *
        (_root_.RHTower.weilAtomSymbol (twistWeight χ) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) +
          Real.log q) =
      (∫ τ : ℝ, ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 *
          _root_.RHTower.weilAtomSymbol (twistWeight χ) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) +
        Real.log q * ∫ τ : ℝ, ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 := by
    rw [← integral_const_mul, ← integral_add hS hB]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    show ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 *
        (_root_.RHTower.weilAtomSymbol (twistWeight χ) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) +
          Real.log q) =
      ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 *
          _root_.RHTower.weilAtomSymbol (twistWeight χ) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) +
        Real.log q * ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2
    ring
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [systemForm, hsplit, integral_weilAtomSymbol_twist_packet hq hprim hf hfs]
  field_simp
  ring

/-- **The twisted part is bounded below by the conductor.** If `ψ(x) ≤ Kx + B`, then for every
primitive character of conductor `q` and every packet supported in `[−a, a]`,
`Z_χ(f) ≥ (log q − A₀ − K e^{a} − B − (1 + 2a)²) ∫ f²`. -/
theorem twistedZeroSum_ge_of_psi [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) {K B : ℝ} (hψ : ∀ x : ℝ, 0 ≤ x → Chebyshev.psi x ≤ K * x + B)
    {a : ℝ} (ha : 0 ≤ a) (hf : ContDiff ℝ 2 f)
    (hfs : tsupport (fun u => (f u : ℂ)) ⊆ Icc (-a) a) :
    (Real.log q - archConstant - K * Real.exp a - B - (1 + 2 * a) ^ 2) * ∫ u, f u ^ 2 ≤
      twistedZeroSum hq hprim f := by
  have h := systemForm_ge_of_dominated hψ ha (contDiff_ofReal_packet hf) hfs
    (dominated_twistWeight χ) q
  rw [integral_norm_ofReal_sq] at h
  rw [twistedZeroSum_eq_systemForm hq hprim hf hfs]
  linarith [placeEnergy_nonneg χ fun u => (f u : ℂ)]

/-- The same bound on a packet of aperture `a` with any centre. -/
theorem twistedZeroSum_ge_of_psi_of_short [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) {K B : ℝ} (hψ : ∀ x : ℝ, 0 ≤ x → Chebyshev.psi x ≤ K * x + B)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {c a : ℝ} (ha : 0 ≤ a)
    (hshort : ∀ u, a < |u - c| → f u = 0) :
    (Real.log q - archConstant - K * Real.exp a - B - (1 + 2 * a) ^ 2) * ∫ u, f u ^ 2 ≤
      twistedZeroSum hq hprim f := by
  have hg : ContDiff ℝ 2 fun u => f (u - -c) := hf.comp (contDiff_id.sub contDiff_const)
  have hg0 : ∀ x : ℝ, a < |x| → f (x - -c) = 0 := fun x hx =>
    hshort _ (by rwa [sub_neg_eq_add, add_sub_cancel_right])
  have hts : tsupport (fun x => ((f (x - -c) : ℝ) : ℂ)) ⊆ Icc (-a) a := by
    refine closure_minimal (fun x hx => ?_) isClosed_Icc
    by_contra hxI
    have hx' : a < |x| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hxI
      rcases hxI with h | h
      · exact lt_abs.mpr (Or.inr (by linarith))
      · exact lt_abs.mpr (Or.inl h)
    exact hx (by
      show ((f (x - -c) : ℝ) : ℂ) = 0
      rw [hg0 x hx', Complex.ofReal_zero])
  have h := twistedZeroSum_ge_of_psi hq hprim hψ ha hg hts
  have hmass : ∫ u, f (u - -c) ^ 2 = ∫ u, f u ^ 2 :=
    integral_sub_right_eq_self (fun u => f u ^ 2) (-c)
  rwa [twistedZeroSum_translate hq hprim hf hfc (-c), hmass] at h

/-- **The trivial aperture with the constant of the prime number theorem.** For every `ε > 0`
there is `B` such that for every primitive character of conductor `q` and every packet of
aperture `a`: `Z_χ(f) ≥ (log q − (1 + ε) e^{a} − (1 + 2a)² − B) ∫ f²`. -/
theorem exists_twistedZeroSum_ge {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, ∀ {q : ℕ} [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
      (hprim : χ.IsPrimitive) {f : ℝ → ℝ}, ContDiff ℝ 2 f → HasCompactSupport f →
      ∀ {c a : ℝ}, 0 ≤ a → (∀ u, a < |u - c| → f u = 0) →
        (Real.log q - (1 + ε) * Real.exp a - (1 + 2 * a) ^ 2 - B) * ∫ u, f u ^ 2 ≤
          twistedZeroSum hq hprim f := by
  obtain ⟨B, hB⟩ := exists_psi_le_linear hε
  refine ⟨archConstant + B, fun hq _ hprim _ hf hfc _ _ ha hshort => ?_⟩
  have h := twistedZeroSum_ge_of_psi_of_short hq hprim hB hf hfc ha hshort
  linarith

/-- For every `c > 0` and `B`, eventually `B + (1 + 2 log x)² ≤ c x`. -/
theorem eventually_const_add_log_sq_le {c : ℝ} (hc : 0 < c) (B : ℝ) :
    ∀ᶠ x : ℝ in atTop, B + (1 + 2 * Real.log x) ^ 2 ≤ c * x := by
  have h0 : (fun _ : ℝ => B + 1) =o[atTop] (id : ℝ → ℝ) :=
    Asymptotics.isLittleO_const_id_atTop _
  have h1 : (fun x : ℝ => Real.log x ^ 1) =o[atTop] (id : ℝ → ℝ) :=
    Real.isLittleO_pow_log_id_atTop
  have h2 : (fun x : ℝ => Real.log x ^ 2) =o[atTop] (id : ℝ → ℝ) :=
    Real.isLittleO_pow_log_id_atTop
  have hsum : (fun x : ℝ => B + 1 + (4 * Real.log x ^ 1 + 4 * Real.log x ^ 2)) =o[atTop]
      (id : ℝ → ℝ) := h0.add ((h1.const_mul_left 4).add (h2.const_mul_left 4))
  filter_upwards [hsum.def hc, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  rw [Real.norm_eq_abs, id, Real.norm_eq_abs, abs_of_nonneg hx0] at hx
  have := (le_abs_self _).trans hx
  nlinarith

/-- **The trivial aperture of a conductor is at least `log log q − o(1)`.** For every `η > 0`
there is `M₀` such that for every primitive character of conductor `q` with `log q ≥ M₀` and
every packet of aperture `a ≤ log log q − η`:
`Z_χ(f) ≥ ½ (1 − e^{−η/2}) log q ∫ f²`. -/
theorem exists_trivialAperture_margin {η : ℝ} (hη : 0 < η) :
    ∃ M₀ : ℝ, ∀ {q : ℕ} [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
      (hprim : χ.IsPrimitive), M₀ ≤ Real.log q → ∀ {f : ℝ → ℝ}, ContDiff ℝ 2 f →
      HasCompactSupport f → ∀ {c a : ℝ}, 0 ≤ a → a ≤ Real.log (Real.log q) - η →
      (∀ u, a < |u - c| → f u = 0) →
        (1 - Real.exp (-η / 2)) / 2 * Real.log q * ∫ u, f u ^ 2 ≤ twistedZeroSum hq hprim f := by
  have hδ : 0 < 1 - Real.exp (-η / 2) := by
    have : Real.exp (-η / 2) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_zero] at this
    linarith
  have hε : 0 < Real.exp (η / 2) - 1 := by
    have : Real.exp 0 < Real.exp (η / 2) := Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_zero] at this
    linarith
  obtain ⟨B, hB⟩ := exists_twistedZeroSum_ge hε
  obtain ⟨M₁, hM₁⟩ := eventually_atTop.mp
    (eventually_const_add_log_sq_le (half_pos hδ) B)
  refine ⟨max M₁ 1, fun {q} _ hq _ hprim hM f hf hfc _ a ha0 ha hshort => ?_⟩
  set x := Real.log q with hx
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hM
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have ha' : a ≤ Real.log x := by linarith
  -- the prime side: `(1 + ε) e^{a} ≤ e^{−η/2} log q`
  have hexp : (1 + (Real.exp (η / 2) - 1)) * Real.exp a ≤ Real.exp (-η / 2) * x := by
    have h1 : Real.exp a ≤ Real.exp (Real.log x - η) := Real.exp_le_exp.mpr ha
    rw [Real.exp_sub, Real.exp_log hx0] at h1
    have h2 : Real.exp (η / 2) * (x / Real.exp η) = Real.exp (-η / 2) * x := by
      rw [show -η / 2 = η / 2 - η by ring, Real.exp_sub]
      ring
    calc (1 + (Real.exp (η / 2) - 1)) * Real.exp a = Real.exp (η / 2) * Real.exp a := by ring
      _ ≤ Real.exp (η / 2) * (x / Real.exp η) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = Real.exp (-η / 2) * x := h2
  -- the lower-order terms
  have hlow : B + (1 + 2 * a) ^ 2 ≤ (1 - Real.exp (-η / 2)) / 2 * x := by
    have h := hM₁ x (le_trans (le_max_left _ _) hM)
    nlinarith
  have hmass : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  refine le_trans (mul_le_mul_of_nonneg_right ?_ hmass) (hB hq hprim hf hfc ha0 hshort)
  linarith

end GaloisForLFunctions.SelectiveArithmetic
