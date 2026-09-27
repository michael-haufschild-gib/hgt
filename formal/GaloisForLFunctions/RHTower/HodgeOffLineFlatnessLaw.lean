import GaloisForLFunctions.RHTower.RadicalDetectionKernel

/-!
# The level-`a` Hodge index forces super-exponential flatness at off-line zeros

Let `ρ₀` be a nontrivial zero off the critical line, `γ₀ = gammaOf ρ₀`, `γ₁ = conj γ₀`, and let
`h` be the detection kernel of the pair (`RadicalDetectionKernel`). Its transform vanishes at every
zero except `γ₀, γ₁`. The test

`f = N P (χ_{a-1/4} h)`

truncates `h` smoothly to `[-(a-1/4), a-1/4]`. The polar operator `P` makes `f̂(±i/2) = 0` exactly,
and the node operator `N` interpolates `N(γ₀) = 1`, `N(γ₁) = v`, with `|v| = 1` chosen so that the
pair contributes the negative hyperbolic block `-(m_{ρ₀} + m_{ρ̄₀'})|X₀||X₁|`, where
`X_j = P(γ_j) ĥ(γ_j)`. Every other zero sees only the discarded tail (`re_W_le_node_add`).

Hence, if the level-`a` Hodge index holds (`node_inequality`, `flatness`),

`|X₀||X₁| ≤ C 4^n (1 + 1/|Im γ₀|)² (1+|γ₀|)² e^{a/2} · ε_Φ(a) · G_Φ`,

where `ε_Φ(a)` is the tail of Riemann's kernel beyond `a - 3/8`, of size
`exp(-π e^{2a - 3/4} + O(na))`. Since `|ĥ(γ_j)|` is `|ξ^{(m)}(ρ₀)/m!|` up to powers of
`2|Im γ₀|`, and is of order `e^{-π|γ₀|/4}` times the local Taylor coefficient of `ζ`, the Hodge
index at level `a` can hold only if every off-line zero below the height `≈ 2e^{2a-3/4}` is
super-exponentially flat.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

local notation "Φ" => riemannPhiKernel

/-! ## Splitting the Weil sum at one off-line pair -/

/-- `S_Z = Σ m_ρ/(1+|γ_ρ|²)`, the unconditional zero sum. -/
def zeroSumZ : ℝ :=
  ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))

theorem summable_zeroSumZ : Summable (fun ρ : zetaZeroConfig.carrier =>
    (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
  have := WeilEF.zero_sum_inv_sq zetaSeam
  simpa [zetaZeroConfig] using this

theorem zeroSumZ_nonneg : 0 ≤ zeroSumZ :=
  tsum_nonneg fun _ => div_nonneg (Nat.cast_nonneg _)
    (add_pos_of_pos_of_nonneg one_pos (Complex.normSq_nonneg _)).le

theorem gammaOf_injective : Function.Injective gammaOf := by
  intro x y h
  unfold gammaOf at h
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have := (div_left_inj' hI).mp h
  linear_combination this

theorem reflect_reflect (ρ : ℂ) : Zeta23.reflect (Zeta23.reflect ρ) = ρ := by
  unfold Zeta23.reflect; simp

/-- **One off-line pair against the rest.** For a `C²` test supported in `[-a,a]` whose transform
is at most `η` at every zero other than `ρ₀, ρ₁` (with `γ_{ρ₁} = conj γ_{ρ₀}`),
`Re W(f,f) ≤ (m₀+m₁) Re(f̂(γ₀) conj f̂(γ₁)) + (5/4) S_Z η e^{a/2} 4(‖f‖₁+‖f''‖₁)`. -/
theorem re_W_le_node_add {f : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a) (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ a) {ρ₀ ρ₁ : ℂ} (h₀ : ρ₀ ∈ zetaZeroConfig.carrier)
    (h₁ : ρ₁ ∈ zetaZeroConfig.carrier) (hne : ρ₀ ≠ ρ₁)
    (hconj : gammaOf ρ₁ = (starRingEnd ℂ) (gammaOf ρ₀)) {η : ℝ} (hη : 0 ≤ η)
    (hother : ∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → ρ ≠ ρ₁ → ‖paperFT f (gammaOf ρ)‖ ≤ η) :
    (zetaZeroConfig.W f f).re ≤
      ((zetaZeroConfig.mult ρ₀ : ℝ) + zetaZeroConfig.mult ρ₁) *
        (paperFT f (gammaOf ρ₀) * (starRingEnd ℂ) (paperFT f (gammaOf ρ₁))).re +
      (5 / 4) * zeroSumZ * (η * (Real.exp (a / 2) *
        (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)))) := by
  set N : ℝ := 4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖) with hN
  have hN1 : 0 ≤ ∫ u, ‖f u‖ := integral_nonneg fun u => norm_nonneg _
  have hN2 : 0 ≤ ∫ u, ‖deriv (deriv f) u‖ := integral_nonneg fun u => norm_nonneg _
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  set E : ℝ := Real.exp (a / 2) * N with hE
  have hE0 : 0 ≤ E := by positivity
  have hdec : ∀ ρ : ℂ, ∀ z : ℂ, |z.im| ≤ 1 / 2 → |z.re| = |ρ.im| →
      ‖paperFT f z‖ ≤ E * (1 / (1 + |ρ.im|) ^ 2) := by
    intro ρ z hz hre
    have h := norm_paperFT_le_decay hf hsupp z
    rw [hre] at h
    refine h.trans ?_
    have hea : Real.exp (|z.im| * a) ≤ Real.exp (a / 2) :=
      Real.exp_le_exp.mpr (by nlinarith [abs_nonneg z.im])
    calc Real.exp (|z.im| * a) * N / (1 + |ρ.im|) ^ 2
        ≤ Real.exp (a / 2) * N / (1 + |ρ.im|) ^ 2 := by gcongr
      _ = E * (1 / (1 + |ρ.im|) ^ 2) := by rw [hE]; ring
  have hpt : ∀ ρ : zetaZeroConfig.carrier, |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 ∧
      |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 ∧
      |(gammaOf (ρ : ℂ)).re| = |(ρ : ℂ).im| ∧
      |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).re| = |(ρ : ℂ).im| := by
    intro ρ
    have hstrip : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
      have h : IsNontrivialZero (ρ : ℂ) := ρ.2
      exact ⟨h.2.1, h.2.2⟩
    have hIm := (WeilEF.abs_gammaOf_im_lt hstrip).le
    refine ⟨hIm, by rw [Complex.conj_im, abs_neg]; exact hIm, by rw [WeilEF.gammaOf_re],
      by rw [Complex.conj_re, WeilEF.gammaOf_re]⟩
  have hq : ∀ ρ : zetaZeroConfig.carrier, 1 / (1 + |(ρ : ℂ).im|) ^ 2 ≤
      (5 / 4) * (1 / (1 + Complex.normSq (gammaOf ρ))) := by
    intro ρ
    have hstrip := zetaZeroConfig.strip ρ ρ.2
    exact one_div_one_add_abs_im_sq_le hstrip
  set ws : zetaZeroConfig.carrier → ℂ := fun ρ => zetaZeroConfig.Wsummand f f ρ with hws
  have hwsn : ∀ ρ : zetaZeroConfig.carrier, ‖ws ρ‖ = (zetaZeroConfig.mult ρ : ℝ) *
      ‖paperFT f (gammaOf ρ)‖ * ‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖ := by
    intro ρ
    simp only [hws, ZeroConfig.Wsummand]
    rw [norm_mul, norm_mul, Complex.norm_natCast, RCLike.norm_conj]
  have hsum := summable_zeroSumZ
  have hall : ∀ ρ : zetaZeroConfig.carrier, ‖ws ρ‖ ≤ (5 / 4) * (E * E) *
      ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
    intro ρ
    obtain ⟨h1, h2, h3, h4⟩ := hpt ρ
    have b1 := hdec (ρ : ℂ) _ h1 h3
    have b2 := hdec (ρ : ℂ) _ h2 h4
    have hle1 : 1 / (1 + |(ρ : ℂ).im|) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith [abs_nonneg (ρ : ℂ).im]
    have b1' : ‖paperFT f (gammaOf ρ)‖ ≤ E := b1.trans (by nlinarith)
    rw [hwsn]
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    calc (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ)‖ *
          ‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖
        ≤ (zetaZeroConfig.mult ρ : ℝ) * E * (E * ((5 / 4) * (1 / (1 + Complex.normSq (gammaOf ρ))))) := by
          gcongr
          exact b2.trans (mul_le_mul_of_nonneg_left (hq ρ) hE0)
      _ = (5 / 4) * (E * E) * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
          ring
  have hsumws : Summable ws :=
    Summable.of_norm_bounded (hsum.mul_left _) hall
  -- the node pair as a finset of the carrier
  set p₀ : zetaZeroConfig.carrier := ⟨ρ₀, h₀⟩
  set p₁ : zetaZeroConfig.carrier := ⟨ρ₁, h₁⟩
  have hp : p₀ ≠ p₁ := fun h => hne (congrArg Subtype.val h)
  classical
  set T : Set zetaZeroConfig.carrier :=
    ((↑({p₀, p₁} : Finset zetaZeroConfig.carrier) : Set zetaZeroConfig.carrier)ᶜ) with hT
  have hsplit : ws p₀ + ws p₁ + ∑' x : T, ws x = ∑' ρ, ws ρ := by
    have := hsumws.sum_add_tsum_compl (s := {p₀, p₁})
    rwa [Finset.sum_pair hp] at this
  have hW : zetaZeroConfig.W f f = ws p₀ + ws p₁ + ∑' x : T, ws x := by
    unfold ZeroConfig.W; rw [hsplit]
  -- node part
  have hnode : (ws p₀ + ws p₁).re = ((zetaZeroConfig.mult ρ₀ : ℝ) + zetaZeroConfig.mult ρ₁) *
      (paperFT f (gammaOf ρ₀) * (starRingEnd ℂ) (paperFT f (gammaOf ρ₁))).re := by
    have hc1 : (starRingEnd ℂ) (gammaOf ρ₁) = gammaOf ρ₀ := by rw [hconj]; simp
    simp only [hws, ZeroConfig.Wsummand, p₀, p₁]
    rw [← hconj, hc1]
    set A := paperFT f (gammaOf ρ₀)
    set B := paperFT f (gammaOf ρ₁)
    have hre : (B * (starRingEnd ℂ) A).re = (A * (starRingEnd ℂ) B).re := by
      rw [show B * (starRingEnd ℂ) A = (starRingEnd ℂ) (A * (starRingEnd ℂ) B) by simp [mul_comm],
        Complex.conj_re]
    have e0 : (zetaZeroConfig.mult ρ₀ : ℂ) * A * (starRingEnd ℂ) B =
        ((zetaZeroConfig.mult ρ₀ : ℝ) : ℂ) * (A * (starRingEnd ℂ) B) := by push_cast; ring
    have e1 : (zetaZeroConfig.mult ρ₁ : ℂ) * B * (starRingEnd ℂ) A =
        ((zetaZeroConfig.mult ρ₁ : ℝ) : ℂ) * (B * (starRingEnd ℂ) A) := by push_cast; ring
    rw [e0, e1, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, hre]
    ring
  -- rest
  have hrest : (∑' x : T, ws x).re ≤ (5 / 4) * zeroSumZ * (η * E) := by
    have hb : ∀ x : T, ‖ws x‖ ≤ (5 / 4) * (η * E) *
        ((zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) /
          (1 + Complex.normSq (gammaOf (x : zetaZeroConfig.carrier)))) := by
      intro x
      have hx := x.2
      simp only [T, Set.mem_compl_iff, Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
      have hx0 : ((x : zetaZeroConfig.carrier) : ℂ) ≠ ρ₀ := fun h => hx.1 (Subtype.ext h)
      have hx1 : ((x : zetaZeroConfig.carrier) : ℂ) ≠ ρ₁ := fun h => hx.2 (Subtype.ext h)
      obtain ⟨h1, h2, h3, h4⟩ := hpt (x : zetaZeroConfig.carrier)
      have b1 := hother _ (x : zetaZeroConfig.carrier).2 hx0 hx1
      have b2 := hdec _ _ h2 h4
      rw [hwsn]
      have hm : (0 : ℝ) ≤ zetaZeroConfig.mult (x : zetaZeroConfig.carrier) := Nat.cast_nonneg _
      calc (zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) *
            ‖paperFT f (gammaOf (x : zetaZeroConfig.carrier))‖ *
            ‖paperFT f ((starRingEnd ℂ) (gammaOf (x : zetaZeroConfig.carrier)))‖
          ≤ (zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) * η *
              (E * ((5 / 4) * (1 / (1 + Complex.normSq (gammaOf (x : zetaZeroConfig.carrier)))))) := by
            gcongr
            exact b2.trans (mul_le_mul_of_nonneg_left (hq _) hE0)
        _ = (5 / 4) * (η * E) * ((zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) /
              (1 + Complex.normSq (gammaOf (x : zetaZeroConfig.carrier)))) := by ring
    have hsT : Summable (fun x : T => (5 / 4) * (η * E) *
        ((zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) /
          (1 + Complex.normSq (gammaOf (x : zetaZeroConfig.carrier))))) :=
      (hsum.subtype T).mul_left _
    have hwsT : Summable (fun x : T => ‖ws x‖) := Summable.of_nonneg_of_le
      (fun _ => norm_nonneg _) hb hsT
    calc (∑' x : T, ws x).re ≤ ‖∑' x : T, ws x‖ := Complex.re_le_norm _
      _ ≤ ∑' x : T, ‖ws x‖ := norm_tsum_le_tsum_norm hwsT
      _ ≤ ∑' x : T, (5 / 4) * (η * E) *
            ((zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) /
              (1 + Complex.normSq (gammaOf (x : zetaZeroConfig.carrier)))) :=
          Summable.tsum_le_tsum hb hwsT hsT
      _ = (5 / 4) * (η * E) * ∑' x : T,
            ((zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) /
              (1 + Complex.normSq (gammaOf (x : zetaZeroConfig.carrier)))) := tsum_mul_left
      _ ≤ (5 / 4) * (η * E) * zeroSumZ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Summable.tsum_subtype_le (fun ρ : zetaZeroConfig.carrier =>
            (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) T
            (fun _ => div_nonneg (Nat.cast_nonneg _)
              (add_pos_of_pos_of_nonneg one_pos (Complex.normSq_nonneg _)).le) hsum
      _ = (5 / 4) * zeroSumZ * (η * E) := by ring
  rw [hW, Complex.add_re, hnode]
  linarith

theorem cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self x)
  have h2 : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.mpr (neg_le_abs x)
  linarith

theorem norm_cexp_I_mul_real_le {z : ℂ} (hz : |z.im| ≤ 1 / 2) {t : ℝ} (ht : 0 ≤ t) :
    ‖Complex.exp (I * z * t)‖ ≤ Real.exp (t / 2) := by
  rw [norm_cexp_I_mul_eq]
  apply Real.exp_le_exp.mpr
  have : -(z.im * t) ≤ |z.im| * t := by
    have := neg_abs_le z.im; nlinarith
  nlinarith

theorem norm_polarSymbol_le {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖polarSymbol s z‖ ≤ 2 * Real.exp (s / 2) := by
  unfold polarSymbol
  have h1 := norm_cexp_I_mul_real_le hz hs
  have h2 : ‖Complex.exp (-(I * z * s))‖ ≤ Real.exp (s / 2) := by
    have hz' : |(-z).im| ≤ 1 / 2 := by rw [Complex.neg_im, abs_neg]; exact hz
    have := norm_cexp_I_mul_real_le hz' hs
    rwa [show I * -z * (s : ℂ) = -(I * z * s) by ring] at this
  have hc : ‖((Real.cosh (s / 2) : ℝ) : ℂ)‖ ≤ Real.exp (s / 2) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]
    have := cosh_le_exp_abs (s / 2); rwa [abs_of_nonneg (by linarith)] at this
  calc ‖(Complex.exp (I * z * s) + Complex.exp (-(I * z * s))) / 2 - ((Real.cosh (s / 2) : ℝ) : ℂ)‖
      ≤ ‖(Complex.exp (I * z * s) + Complex.exp (-(I * z * s))) / 2‖ +
          ‖((Real.cosh (s / 2) : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ ≤ (Real.exp (s / 2) + Real.exp (s / 2)) / 2 + Real.exp (s / 2) := by
        rw [norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
        gcongr
        exact (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = 2 * Real.exp (s / 2) := by ring

theorem norm_nodeSymbol_le (c₁ c₂ : ℂ) {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖nodeSymbol c₁ c₂ s z‖ ≤ ‖c₁‖ + ‖c₂‖ * Real.exp (s / 2) := by
  unfold nodeSymbol
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  gcongr
  exact norm_cexp_I_mul_real_le hz hs

theorem SuperExpDecay.polarOp {g : ℝ → ℂ} (hg : SuperExpDecay g) (s : ℝ) :
    SuperExpDecay (RHTower.polarOp s g) := by
  have h1 := hg.comp_sub s
  have h2 := hg.comp_sub (-s)
  have h3 := ((h1.add h2).const_mul (1 / 2 : ℂ)).sub (hg.const_mul ((Real.cosh (s / 2) : ℝ) : ℂ))
  have e : (fun u => (1 / 2 : ℂ) * ((fun u => g (u - s)) + fun u => g (u - -s)) u -
      ((Real.cosh (s / 2) : ℝ) : ℂ) * g u) = RHTower.polarOp s g := by
    funext u; unfold RHTower.polarOp; simp only [Pi.add_apply, sub_neg_eq_add]; ring
  rw [e] at h3; exact h3

theorem SuperExpDecay.nodeOp {g : ℝ → ℂ} (hg : SuperExpDecay g) (c₁ c₂ : ℂ) (s : ℝ) :
    SuperExpDecay (RHTower.nodeOp c₁ c₂ s g) := by
  have h := (hg.const_mul c₁).add ((hg.comp_sub s).const_mul c₂)
  have e : ((fun u => c₁ * g u) + fun u => c₂ * g (u - s)) = RHTower.nodeOp c₁ c₂ s g := by
    funext u; rfl
  rw [e] at h; exact h

namespace OffLinePairData

variable (D : OffLinePairData)

/-- The shift and plateau width used by the test. -/
def sh : ℝ := 1 / 8

theorem sh_pos : 0 < sh := by norm_num [sh]

/-- The truncated kernel `χ_b h`. -/
def trunc (b : ℝ) : ℝ → ℂ := fun x => ((plateau b sh x : ℝ) : ℂ) * D.kernel x

/-- The discarded tail `(1 - χ_b) h`. -/
def tailPart (b : ℝ) : ℝ → ℂ := fun x => (1 - ((plateau b sh x : ℝ) : ℂ)) * D.kernel x

theorem norm_plateau_le (b x : ℝ) : ‖((plateau b sh x : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (plateau_nonneg _ _ _)]
  exact plateau_le_one _ _ _

theorem norm_one_sub_plateau_le (b x : ℝ) : ‖1 - ((plateau b sh x : ℝ) : ℂ)‖ ≤ 1 := by
  rw [show (1 : ℂ) - ((plateau b sh x : ℝ) : ℂ) = ((1 - plateau b sh x : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [plateau_le_one b sh x])]
  linarith [plateau_nonneg b sh x]

theorem continuous_plateauC (b : ℝ) : Continuous fun x => ((plateau b sh x : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp (continuous_plateau b sh)

theorem superExpDecay_trunc (b : ℝ) : SuperExpDecay (D.trunc b) :=
  D.superExpDecay_kernel.mul_bounded (continuous_plateauC b) (norm_plateau_le b)

theorem superExpDecay_tailPart (b : ℝ) : SuperExpDecay (D.tailPart b) :=
  D.superExpDecay_kernel.mul_bounded (continuous_const.sub (continuous_plateauC b))
    (norm_one_sub_plateau_le b)

theorem paperFT_trunc (b : ℝ) (z : ℂ) :
    paperFT (D.trunc b) z = paperFT D.kernel z - paperFT (D.tailPart b) z := by
  unfold paperFT
  rw [← integral_sub (D.superExpDecay_kernel.integrable_mul_cexp z)
    ((D.superExpDecay_tailPart b).integrable_mul_cexp z)]
  congr 1; funext x; unfold trunc tailPart; ring

/-- The tail's transform is bounded by the weighted tail of the kernel beyond `b - 1/8`. -/
theorem norm_paperFT_tailPart_le (b : ℝ) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT (D.tailPart b) z‖ ≤ expTail D.kernel (1 / 2) (b - sh) := by
  unfold paperFT expTail
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun u => norm_nonneg _)
    (D.superExpDecay_kernel.integrable_tail _ _) (Eventually.of_forall fun u => ?_))
  simp only [indicator, mem_setOf_eq]
  split_ifs with hu
  · rw [norm_mul]
    unfold tailPart
    rw [norm_mul]
    calc ‖1 - ((plateau b sh u : ℝ) : ℂ)‖ * ‖D.kernel u‖ * ‖Complex.exp (I * z * u)‖
        ≤ 1 * ‖D.kernel u‖ * Real.exp (1 / 2 * |u|) := by
          gcongr
          · exact norm_one_sub_plateau_le b u
          · exact norm_cexp_I_mul_le_exp hz u
      _ = ‖D.kernel u‖ * Real.exp (1 / 2 * |u|) := by ring
  · push Not at hu
    have hp : plateau b sh u = 1 := plateau_eq_one sh_pos (by linarith)
    unfold tailPart
    simp [hp]

/-! ### The interpolation coefficients -/

/-- `Q = P(γ₀)ĥ(γ₀) · conj(P(γ₁)ĥ(γ₁))`. -/
def Qval : ℂ := (polarSymbol sh D.γ₀ * paperFT D.kernel D.γ₀) *
  (starRingEnd ℂ) (polarSymbol sh D.γ₁ * paperFT D.kernel D.γ₁)

/-- The unimodular value `v` with `Q conj v = -|Q|`. -/
def vval : ℂ := if D.Qval = 0 then 1 else -(D.Qval / (‖D.Qval‖ : ℂ))

theorem norm_vval : ‖D.vval‖ = 1 := by
  unfold vval
  split_ifs with h
  · simp
  · rw [norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      div_self (norm_ne_zero_iff.mpr h)]

theorem Qval_mul_conj_vval : D.Qval * (starRingEnd ℂ) D.vval = -(‖D.Qval‖ : ℂ) := by
  unfold vval
  split_ifs with h
  · simp [h]
  · have hn : (‖D.Qval‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
    rw [map_neg, map_div₀, Complex.conj_ofReal, mul_neg, ← mul_div_assoc, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    field_simp
    push_cast; ring

/-- `e^{iγ₀s} - e^{iγ₁s}`. -/
def expGap : ℂ := Complex.exp (I * D.γ₀ * sh) - Complex.exp (I * D.γ₁ * sh)

theorem norm_expGap_ge : 2 * sh * |D.γ₀.im| ≤ ‖D.expGap‖ := by
  unfold expGap
  refine le_trans ?_ (abs_norm_sub_norm_le _ _)
  rw [norm_cexp_I_mul_eq, norm_cexp_I_mul_eq]
  have hγ₁ : D.γ₁.im = -D.γ₀.im := by simp [γ₁]
  rw [hγ₁]
  set x := D.γ₀.im * sh with hx
  have hsh : 0 < sh := sh_pos
  have key : ∀ y : ℝ, 0 ≤ y → 2 * y ≤ |Real.exp (-y) - Real.exp y| := by
    intro y hy
    have h1 : y ≤ Real.sinh y := Real.self_le_sinh_iff.mpr hy
    rw [Real.sinh_eq] at h1
    rw [abs_of_nonpos (by linarith [Real.exp_le_exp.mpr (show -y ≤ y by linarith)])]
    linarith
  have hxabs : |x| = sh * |D.γ₀.im| := by rw [hx, abs_mul, abs_of_pos hsh]; ring
  rcases le_or_gt 0 x with h0 | h0
  · have := key x h0
    rw [show -(-D.γ₀.im * sh) = x by rw [hx]; ring, show -(D.γ₀.im * sh) = -x by rw [hx]]
    rw [abs_of_nonneg h0] at hxabs
    linarith
  · have := key (-x) (by linarith)
    rw [show -(-D.γ₀.im * sh) = x by rw [hx]; ring, show -(D.γ₀.im * sh) = -x by rw [hx]]
    rw [neg_neg, abs_sub_comm] at this
    rw [abs_of_neg h0] at hxabs
    linarith

theorem expGap_ne_zero : D.expGap ≠ 0 := by
  intro h
  have h1 := D.norm_expGap_ge
  rw [h, norm_zero] at h1
  have : 0 < 2 * sh * |D.γ₀.im| := by
    have := sh_pos; have := abs_pos.mpr D.him; positivity
  linarith

def c₂ : ℂ := (1 - D.vval) / D.expGap

def c₁ : ℂ := 1 - D.c₂ * Complex.exp (I * D.γ₀ * sh)

theorem nodeSymbol_γ₀ : nodeSymbol D.c₁ D.c₂ sh D.γ₀ = 1 := by
  unfold nodeSymbol c₁; ring

theorem nodeSymbol_γ₁ : nodeSymbol D.c₁ D.c₂ sh D.γ₁ = D.vval := by
  have key : D.c₂ * D.expGap = 1 - D.vval := div_mul_cancel₀ _ D.expGap_ne_zero
  unfold nodeSymbol c₁
  unfold expGap at key
  linear_combination (-1 : ℂ) * key

theorem norm_c₂_le : ‖D.c₂‖ ≤ 1 / (sh * |D.γ₀.im|) := by
  unfold c₂
  have hg := D.norm_expGap_ge
  have hpos : 0 < 2 * sh * |D.γ₀.im| := by
    have := sh_pos; have := abs_pos.mpr D.him; positivity
  rw [norm_div]
  have hnum : ‖1 - D.vval‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [D.norm_vval]; norm_num)
  calc ‖1 - D.vval‖ / ‖D.expGap‖ ≤ 2 / (2 * sh * |D.γ₀.im|) := by
        gcongr
    _ = 1 / (sh * |D.γ₀.im|) := by field_simp

theorem norm_c₁_le : ‖D.c₁‖ ≤ 1 + Real.exp (sh / 2) / (sh * |D.γ₀.im|) := by
  unfold c₁
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one, norm_mul]
  have h1 := D.norm_c₂_le
  have h2 := norm_cexp_I_mul_real_le D.him2 sh_pos.le
  have : ‖D.c₂‖ * ‖Complex.exp (I * D.γ₀ * sh)‖ ≤ 1 / (sh * |D.γ₀.im|) * Real.exp (sh / 2) :=
    mul_le_mul h1 h2 (norm_nonneg _) (by have := sh_pos; have := abs_pos.mpr D.him; positivity)
  rw [div_mul_eq_mul_div, one_mul] at this
  linarith

/-! ### The test -/

/-- **The detection test at level `a`.** -/
def test (a : ℝ) : ℝ → ℂ := nodeOp D.c₁ D.c₂ sh (polarOp sh (D.trunc (a - 1 / 4)))

theorem paperFT_test (a : ℝ) (z : ℂ) :
    paperFT (D.test a) z = nodeSymbol D.c₁ D.c₂ sh z * polarSymbol sh z *
      (paperFT D.kernel z - paperFT (D.tailPart (a - 1 / 4)) z) := by
  have ht := D.superExpDecay_trunc (a - 1 / 4)
  have hp := ht.polarOp sh
  unfold test
  rw [paperFT_nodeOp (hp.integrable_mul_cexp z), paperFT_polarOp (ht.integrable_mul_cexp z),
    paperFT_trunc]
  ring

theorem paperFT_test_half_I (a : ℝ) : paperFT (D.test a) (I / 2) = 0 := by
  rw [paperFT_test, polarSymbol_half_I]; ring

theorem paperFT_test_neg_half_I (a : ℝ) : paperFT (D.test a) (-(I / 2)) = 0 := by
  rw [paperFT_test, polarSymbol_neg_half_I]; ring

theorem trunc_eq_zero {b u : ℝ} (hu : b ≤ |u|) : D.trunc b u = 0 := by
  unfold trunc; rw [plateau_eq_zero sh_pos hu]; simp

theorem test_eq_zero {a u : ℝ} (hu : a ≤ |u|) : D.test a u = 0 := by
  unfold test
  refine nodeOp_eq_zero (b := a - 1 / 4 + sh) sh_pos.le _ _ (fun v hv => ?_) (by unfold sh; linarith)
  exact polarOp_eq_zero sh_pos.le (fun w hw => D.trunc_eq_zero hw) hv

theorem test_supp {a : ℝ} (u : ℝ) (hu : D.test a u ≠ 0) : |u| ≤ a := by
  by_contra h; push Not at h; exact hu (D.test_eq_zero h.le)

theorem tsupport_test (a : ℝ) : tsupport (D.test a) ⊆ Icc (-a) a := by
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  have := D.test_supp u hu
  exact ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩

/-! ### Calculus and norms of the test -/

/-- The constant of the plateau: `2K/w + (2K+2K²)/w² + 2` with `w = 1/8`. -/
theorem exists_plateau_constant : ∃ Kp : ℝ, 2 ≤ Kp ∧ ∀ b x : ℝ,
    |plateau₁ b sh x| ≤ Kp ∧ |plateau₂ b sh x| ≤ Kp := by
  obtain ⟨K, hK1, hK⟩ := exists_smoothTransition_deriv_bound
  refine ⟨2 * K / sh + (2 * K + 2 * K ^ 2) / sh ^ 2 + 2, ?_, fun b x => ⟨?_, ?_⟩⟩
  · have := sh_pos; have : 0 ≤ 2 * K / sh := by positivity
    have : 0 ≤ (2 * K + 2 * K ^ 2) / sh ^ 2 := by positivity
    linarith
  · have h := abs_plateau₁_le (b := b) sh_pos hK x
    have := sh_pos; have : 0 ≤ (2 * K + 2 * K ^ 2) / sh ^ 2 := by positivity
    linarith
  · have h := abs_plateau₂_le (b := b) sh_pos hK x
    have := sh_pos; have : 0 ≤ 2 * K / sh := by positivity
    linarith

/-- `Γ = 1 + |γ₀|` and `G = 2^n ∫ ‖Φ‖ e^{(3n/2)|u|}`. -/
def gNorm : ℝ := 2 ^ D.n * expTail Φ (3 / 2 * D.n) 0

theorem gNorm_nonneg : 0 ≤ D.gNorm := mul_nonneg (by positivity) (expTail_nonneg _ _ _)

/-- The operator norm factor `(‖c₁‖+‖c₂‖)(1+cosh(s/2))`. -/
def opFactor : ℝ := (‖D.c₁‖ + ‖D.c₂‖) * (1 + Real.cosh (sh / 2))

theorem opFactor_nonneg : 0 ≤ D.opFactor := by
  unfold opFactor; have := Real.cosh_pos (sh / 2); positivity

/-- **Calculus of the test.** The test is `C²`, and
`‖f‖₁ + ‖f''‖₁ ≤ 3 Kp · opFactor · (1+|γ₀|)² · G`. -/
theorem test_calculus (a : ℝ) {Kp : ℝ} (hKp2 : 2 ≤ Kp)
    (hKp : ∀ b x : ℝ, |plateau₁ b sh x| ≤ Kp ∧ |plateau₂ b sh x| ≤ Kp) :
    ContDiff ℝ 2 (D.test a) ∧
    (∫ u, ‖D.test a u‖) + (∫ u, ‖deriv (deriv (D.test a)) u‖) ≤
      4 * Kp * D.opFactor * ((1 + ‖D.γ₀‖) ^ 2 * D.gNorm) := by
  obtain ⟨k₁, k₂, hd1, hd2, ck₁, ck₂, ik₁, ik₂, nk₁, nk₂⟩ := D.kernel_calculus
  set b : ℝ := a - 1 / 4 with hb
  set pC : ℝ → ℂ := fun x => ((plateau b sh x : ℝ) : ℂ) with hpC
  set p₁C : ℝ → ℂ := fun x => ((plateau₁ b sh x : ℝ) : ℂ) with hp₁C
  set p₂C : ℝ → ℂ := fun x => ((plateau₂ b sh x : ℝ) : ℂ) with hp₂C
  have hdp : ∀ x, HasDerivAt pC (p₁C x) x := fun x =>
    (hasDerivAt_plateau (b := b) sh_pos.ne' x).ofReal_comp
  have hdp₁ : ∀ x, HasDerivAt p₁C (p₂C x) x := fun x =>
    (hasDerivAt_plateau₁ (b := b) sh_pos.ne' x).ofReal_comp
  have cp : Continuous pC := Complex.continuous_ofReal.comp (continuous_plateau b sh)
  have cp₁ : Continuous p₁C := Complex.continuous_ofReal.comp (continuous_plateau₁ b sh)
  have cp₂ : Continuous p₂C := Complex.continuous_ofReal.comp (continuous_plateau₂ b sh)
  have np : ∀ x, ‖pC x‖ ≤ 1 := fun x => norm_plateau_le b x
  have np₁ : ∀ x, ‖p₁C x‖ ≤ Kp := fun x => by
    simp only [hp₁C, Complex.norm_real, Real.norm_eq_abs]; exact (hKp b x).1
  have np₂ : ∀ x, ‖p₂C x‖ ≤ Kp := fun x => by
    simp only [hp₂C, Complex.norm_real, Real.norm_eq_abs]; exact (hKp b x).2
  set t₁ : ℝ → ℂ := fun x => p₁C x * D.kernel x + pC x * k₁ x with ht₁
  set t₂ : ℝ → ℂ := fun x => p₂C x * D.kernel x + 2 * (p₁C x * k₁ x) + pC x * k₂ x with ht₂
  have hk := D.superExpDecay_kernel
  have hdt : ∀ x, HasDerivAt (D.trunc b) (t₁ x) x := fun x => (hdp x).mul (hd1 x)
  have hdt₁ : ∀ x, HasDerivAt t₁ (t₂ x) x := fun x =>
    (((hdp₁ x).mul (hd1 x)).add ((hdp x).mul (hd2 x))).congr_deriv (by simp only [ht₂]; ring)
  have ckern : Continuous D.kernel := hk.1
  have ct₂ : Continuous t₂ := by simp only [ht₂]; fun_prop
  -- the test and its derivatives
  have hdT : ∀ x, HasDerivAt (D.test a) (nodeOp D.c₁ D.c₂ sh (polarOp sh t₁) x) x :=
    hasDerivAt_nodeOp (hasDerivAt_polarOp hdt sh) D.c₁ D.c₂ sh
  have hdT₁ : ∀ x, HasDerivAt (nodeOp D.c₁ D.c₂ sh (polarOp sh t₁))
      (nodeOp D.c₁ D.c₂ sh (polarOp sh t₂) x) x :=
    hasDerivAt_nodeOp (hasDerivAt_polarOp hdt₁ sh) D.c₁ D.c₂ sh
  have cT₂ : Continuous (nodeOp D.c₁ D.c₂ sh (polarOp sh t₂)) :=
    continuous_nodeOp (continuous_polarOp ct₂ sh) _ _ _
  have hC2 : ContDiff ℝ 2 (D.test a) := contDiff_two_of_hasDerivAt hdT hdT₁ cT₂
  have hD2 : deriv (deriv (D.test a)) = nodeOp D.c₁ D.c₂ sh (polarOp sh t₂) := by
    have h1 : deriv (D.test a) = nodeOp D.c₁ D.c₂ sh (polarOp sh t₁) :=
      funext fun x => (hdT x).deriv
    rw [h1]; exact funext fun x => (hdT₁ x).deriv
  -- norms
  have it₂ : Integrable t₂ := by
    have i1 : Integrable (fun x => p₂C x * D.kernel x) :=
      Integrable.mono' (hk.integrable.norm.const_mul Kp) (cp₂.mul hk.1).aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (np₂ x) (norm_nonneg _))
    have i2' : Integrable (fun x => p₁C x * k₁ x) :=
      Integrable.mono' (ik₁.norm.const_mul Kp) (cp₁.mul ck₁).aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (np₁ x) (norm_nonneg _))
    have i2 : Integrable (fun x => 2 * (p₁C x * k₁ x)) := i2'.const_mul 2
    have i3 : Integrable (fun x => pC x * k₂ x) :=
      Integrable.mono' (ik₂.norm.const_mul 1) (cp.mul ck₂).aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (np x) (norm_nonneg _))
    exact (i1.add i2).add i3
  have nh : ∫ x, ‖D.kernel x‖ ≤ D.gNorm := by
    rw [integral_norm_eq_expTail]; have := D.expTail_kernel_le (c := 0) (X := 0) le_rfl
    simpa [gNorm] using this
  have hG := D.gNorm_nonneg
  have hΓ : 1 ≤ 1 + ‖D.γ₀‖ := by linarith [norm_nonneg D.γ₀]
  have iA : Integrable (fun x => Kp * ‖D.kernel x‖) := hk.integrable.norm.const_mul _
  have iB : Integrable (fun x => 2 * Kp * ‖k₁ x‖) := ik₁.norm.const_mul _
  have iC : Integrable (fun x => ‖k₂ x‖) := ik₂.norm
  have hsum3 : ∫ x, (Kp * ‖D.kernel x‖ + 2 * Kp * ‖k₁ x‖ + ‖k₂ x‖) =
      Kp * (∫ x, ‖D.kernel x‖) + 2 * Kp * (∫ x, ‖k₁ x‖) + ∫ x, ‖k₂ x‖ := by
    have iAB : Integrable (fun x => Kp * ‖D.kernel x‖ + 2 * Kp * ‖k₁ x‖) := iA.add iB
    rw [integral_add iAB iC, integral_add iA iB, integral_const_mul, integral_const_mul]
  have nt₂ : ∫ x, ‖t₂ x‖ ≤ Kp * (∫ x, ‖D.kernel x‖) + 2 * Kp * (∫ x, ‖k₁ x‖) + ∫ x, ‖k₂ x‖ := by
    rw [← hsum3]
    have iABC : Integrable (fun x => Kp * ‖D.kernel x‖ + 2 * Kp * ‖k₁ x‖ + ‖k₂ x‖) :=
      (iA.add iB).add iC
    refine integral_mono it₂.norm iABC fun x => ?_
    simp only [ht₂]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [norm_mul, mul_comm]; exact mul_le_mul_of_nonneg_left (np₂ x) (norm_nonneg _) |>.trans
        (by rw [mul_comm])
    · rw [norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by simp]
      have := mul_le_mul_of_nonneg_right (np₁ x) (norm_nonneg (k₁ x)); linarith
    · rw [norm_mul]; have := mul_le_mul_of_nonneg_right (np x) (norm_nonneg (k₂ x)); linarith
  have ntrunc : ∫ x, ‖D.trunc b x‖ ≤ ∫ x, ‖D.kernel x‖ := by
    refine integral_mono (D.superExpDecay_trunc b).integrable.norm hk.integrable.norm fun x => ?_
    unfold trunc; rw [norm_mul]
    have := mul_le_mul_of_nonneg_right (norm_plateau_le b x) (norm_nonneg (D.kernel x))
    linarith
  have htest : ∫ u, ‖D.test a u‖ ≤ D.opFactor * ∫ x, ‖D.trunc b x‖ := by
    unfold test opFactor
    refine (integral_norm_nodeOp_le ((D.superExpDecay_trunc b).polarOp sh).integrable _ _ _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (integral_norm_polarOp_le (D.superExpDecay_trunc b).integrable sh) (by positivity)
  have htest2 : ∫ u, ‖deriv (deriv (D.test a)) u‖ ≤ D.opFactor * ∫ x, ‖t₂ x‖ := by
    rw [hD2]
    unfold opFactor
    have ip : Integrable (polarOp sh t₂) := by
      have h1 := it₂.comp_sub_right sh
      have h2 := it₂.comp_add_right sh
      have h3 := ((h1.add h2).div_const 2).sub (it₂.const_mul ((Real.cosh (sh / 2) : ℝ) : ℂ))
      refine h3.congr (Eventually.of_forall fun x => ?_)
      simp [polarOp]
    refine (integral_norm_nodeOp_le ip _ _ _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (integral_norm_polarOp_le it₂ sh) (by positivity)
  have hop := D.opFactor_nonneg
  refine ⟨hC2, ?_⟩
  have e1 : ∫ x, ‖t₂ x‖ ≤ (3 * Kp + 1) * ((1 + ‖D.γ₀‖) ^ 2 * D.gNorm) := by
    have hΓ2 : 1 ≤ (1 + ‖D.γ₀‖) ^ 2 := by nlinarith
    have hΓΓ : 1 + ‖D.γ₀‖ ≤ (1 + ‖D.γ₀‖) ^ 2 := by nlinarith
    have nk₁' : ∫ x, ‖k₁ x‖ ≤ (1 + ‖D.γ₀‖) * D.gNorm := nk₁
    have nk₂' : ∫ x, ‖k₂ x‖ ≤ (1 + ‖D.γ₀‖) ^ 2 * D.gNorm := nk₂
    have s1 : Kp * (∫ x, ‖D.kernel x‖) ≤ Kp * ((1 + ‖D.γ₀‖) ^ 2 * D.gNorm) :=
      mul_le_mul_of_nonneg_left (nh.trans (le_mul_of_one_le_left hG hΓ2)) (by linarith)
    have s2 : 2 * Kp * (∫ x, ‖k₁ x‖) ≤ 2 * Kp * ((1 + ‖D.γ₀‖) ^ 2 * D.gNorm) :=
      mul_le_mul_of_nonneg_left (nk₁'.trans (mul_le_mul_of_nonneg_right hΓΓ hG)) (by linarith)
    nlinarith
  have e2 : ∫ x, ‖D.trunc b x‖ ≤ (1 + ‖D.γ₀‖) ^ 2 * D.gNorm := by
    have hΓ2 : 1 ≤ (1 + ‖D.γ₀‖) ^ 2 := by nlinarith
    nlinarith
  calc (∫ u, ‖D.test a u‖) + (∫ u, ‖deriv (deriv (D.test a)) u‖)
      ≤ D.opFactor * ((1 + ‖D.γ₀‖) ^ 2 * D.gNorm) +
          D.opFactor * ((3 * Kp + 1) * ((1 + ‖D.γ₀‖) ^ 2 * D.gNorm)) := by
        gcongr
        · exact htest.trans (mul_le_mul_of_nonneg_left e2 hop)
        · exact htest2.trans (mul_le_mul_of_nonneg_left e1 hop)
    _ ≤ 4 * Kp * D.opFactor * ((1 + ‖D.γ₀‖) ^ 2 * D.gNorm) := by
        have : 0 ≤ D.opFactor * ((1 + ‖D.γ₀‖) ^ 2 * D.gNorm) := by positivity
        nlinarith

/-! ### The node inequality -/

/-- The hyperbolic node block: with `X₀ conj X₁ conj v = -|X₀ conj X₁|` and `|v| = 1`,
`Re((X₀-Y₀) conj(v(X₁-Y₁))) ≤ -|X₀||X₁| + |X₀||Y₁| + |Y₀||X₁| + |Y₀||Y₁|`. -/
theorem re_node_block_le {X₀ X₁ Y₀ Y₁ v : ℂ} (hv : ‖v‖ = 1)
    (hQ : X₀ * (starRingEnd ℂ) X₁ * (starRingEnd ℂ) v = -(‖X₀ * (starRingEnd ℂ) X₁‖ : ℂ)) :
    ((X₀ - Y₀) * (starRingEnd ℂ) (v * (X₁ - Y₁))).re ≤
      -(‖X₀‖ * ‖X₁‖) + ‖X₀‖ * ‖Y₁‖ + ‖Y₀‖ * ‖X₁‖ + ‖Y₀‖ * ‖Y₁‖ := by
  have hexp : (X₀ - Y₀) * (starRingEnd ℂ) (v * (X₁ - Y₁)) =
      X₀ * (starRingEnd ℂ) X₁ * (starRingEnd ℂ) v -
        (starRingEnd ℂ) v * (X₀ * (starRingEnd ℂ) Y₁ + Y₀ * (starRingEnd ℂ) X₁ -
          Y₀ * (starRingEnd ℂ) Y₁) := by
    simp only [map_mul, map_sub]; ring
  rw [hexp, hQ, Complex.sub_re, Complex.neg_re, Complex.ofReal_re, norm_mul, RCLike.norm_conj]
  have hr := Complex.re_le_norm ((starRingEnd ℂ) v * (X₀ * (starRingEnd ℂ) Y₁ +
    Y₀ * (starRingEnd ℂ) X₁ - Y₀ * (starRingEnd ℂ) Y₁))
  have hn : ‖(starRingEnd ℂ) v * (X₀ * (starRingEnd ℂ) Y₁ + Y₀ * (starRingEnd ℂ) X₁ -
      Y₀ * (starRingEnd ℂ) Y₁)‖ ≤ ‖X₀‖ * ‖Y₁‖ + ‖Y₀‖ * ‖X₁‖ + ‖Y₀‖ * ‖Y₁‖ := by
    rw [norm_mul, RCLike.norm_conj, hv, one_mul]
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add_left (norm_add_le (X₀ * (starRingEnd ℂ) Y₁) (Y₀ * (starRingEnd ℂ) X₁))
      ‖Y₀ * (starRingEnd ℂ) Y₁‖).trans ?_
    simp only [norm_mul, RCLike.norm_conj, le_refl]
  have hr2 : -(‖(starRingEnd ℂ) v * (X₀ * (starRingEnd ℂ) Y₁ + Y₀ * (starRingEnd ℂ) X₁ -
      Y₀ * (starRingEnd ℂ) Y₁)‖) ≤ ((starRingEnd ℂ) v * (X₀ * (starRingEnd ℂ) Y₁ +
      Y₀ * (starRingEnd ℂ) X₁ - Y₀ * (starRingEnd ℂ) Y₁)).re := by
    have := Complex.abs_re_le_norm ((starRingEnd ℂ) v * (X₀ * (starRingEnd ℂ) Y₁ +
      Y₀ * (starRingEnd ℂ) X₁ - Y₀ * (starRingEnd ℂ) Y₁))
    have := neg_abs_le ((starRingEnd ℂ) v * (X₀ * (starRingEnd ℂ) Y₁ +
      Y₀ * (starRingEnd ℂ) X₁ - Y₀ * (starRingEnd ℂ) Y₁)).re
    linarith
  linarith

/-- The size `ε = ∫_{|u| ≥ a-3/8} ‖h‖ e^{|u|/2}` of the discarded tail at level `a`. -/
def tailSize (a : ℝ) : ℝ := expTail D.kernel (1 / 2) (a - 1 / 4 - sh)

/-- **The raw node inequality.** If the Hodge index holds at level `a`, the two node values
`X_j = P(γ_j) ĥ(γ_j)` satisfy `|X₀||X₁| ≤ ε'(|X₀|+|X₁|+ε') + R`, where `ε' = 2e^{s/2} ε` is the
tail and `R` is `ε'` times the summed decay of the test over the other zeros. -/
theorem node_inequality {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier) (hγ : gammaOf ρ₀ = D.γ₀)
    {a : ℝ} (ha : 0 ≤ a) (hH : HodgeIndexAtLevel zetaZeroConfig a) :
    ‖polarSymbol sh D.γ₀ * paperFT D.kernel D.γ₀‖ *
        ‖polarSymbol sh D.γ₁ * paperFT D.kernel D.γ₁‖ ≤
      (2 * Real.exp (sh / 2) * D.tailSize a) *
          (‖polarSymbol sh D.γ₀ * paperFT D.kernel D.γ₀‖ +
            ‖polarSymbol sh D.γ₁ * paperFT D.kernel D.γ₁‖ +
            2 * Real.exp (sh / 2) * D.tailSize a) +
        (5 / 4) * zeroSumZ * (((‖D.c₁‖ + ‖D.c₂‖ * Real.exp (sh / 2)) *
          (2 * Real.exp (sh / 2) * D.tailSize a)) * (Real.exp (a / 2) *
            (4 * ((∫ u, ‖D.test a u‖) + ∫ u, ‖deriv (deriv (D.test a)) u‖)))) := by
  obtain ⟨Kp, hKp2, hKp⟩ := exists_plateau_constant
  obtain ⟨hC2, -⟩ := D.test_calculus a hKp2 hKp
  set ε : ℝ := D.tailSize a with hε
  have hε0 : 0 ≤ ε := expTail_nonneg _ _ _
  set ε' : ℝ := 2 * Real.exp (sh / 2) * ε with hε'
  have hε'0 : 0 ≤ ε' := by positivity
  set CN : ℝ := ‖D.c₁‖ + ‖D.c₂‖ * Real.exp (sh / 2) with hCN
  have hCN0 : 0 ≤ CN := by positivity
  -- the second node
  set ρ₁ : ℂ := Zeta23.reflect ρ₀ with hρ₁
  have h₁ : ρ₁ ∈ zetaZeroConfig.carrier := zetaZeroConfig.reflect_mem ρ₀ hρ₀
  have hγ₁ : gammaOf ρ₁ = D.γ₁ := by rw [hρ₁, gammaOf_reflect', hγ]; rfl
  have hne : ρ₀ ≠ ρ₁ := fun h => D.γ₁_ne (by rw [← hγ, ← hγ₁, h])
  have hconj : gammaOf ρ₁ = (starRingEnd ℂ) (gammaOf ρ₀) := by rw [hγ₁, hγ]; rfl
  -- transform bounds
  have hIm : ∀ ρ ∈ zetaZeroConfig.carrier, |(gammaOf ρ).im| ≤ 1 / 2 := by
    intro ρ hρ
    have h : IsNontrivialZero ρ := hρ
    exact (WeilEF.abs_gammaOf_im_lt ⟨h.2.1, h.2.2⟩).le
  have hEb : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖paperFT (D.tailPart (a - 1 / 4)) z‖ ≤ ε :=
    fun z hz => D.norm_paperFT_tailPart_le _ hz
  have hother : ∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → ρ ≠ ρ₁ →
      ‖paperFT (D.test a) (gammaOf ρ)‖ ≤ CN * ε' := by
    intro ρ hρ h0 h1
    have hz0 : gammaOf ρ ≠ D.γ₀ := fun h => h0 (gammaOf_injective (h.trans hγ.symm))
    have hz1 : gammaOf ρ ≠ D.γ₁ := fun h => h1 (gammaOf_injective (h.trans hγ₁.symm))
    have hk0 : paperFT D.kernel (gammaOf ρ) = 0 :=
      D.kernel_eq_zero (riemannXiHat_gammaOf_eq_zero hρ) hz0 hz1
    rw [D.paperFT_test, hk0, zero_sub, norm_mul, norm_mul, norm_neg]
    have hz := hIm ρ hρ
    have n1 := norm_nodeSymbol_le D.c₁ D.c₂ sh_pos.le hz
    have n2 := norm_polarSymbol_le sh_pos.le hz
    have n3 := hEb _ hz
    calc ‖nodeSymbol D.c₁ D.c₂ sh (gammaOf ρ)‖ * ‖polarSymbol sh (gammaOf ρ)‖ *
          ‖paperFT (D.tailPart (a - 1 / 4)) (gammaOf ρ)‖
        ≤ CN * (2 * Real.exp (sh / 2)) * ε := by gcongr
      _ = CN * ε' := by rw [hε']; ring
  have hsplit := re_W_le_node_add ha hC2 D.test_supp hρ₀ h₁ hne hconj
    (mul_nonneg hCN0 hε'0) hother
  -- node values
  set X₀ := polarSymbol sh D.γ₀ * paperFT D.kernel D.γ₀
  set X₁ := polarSymbol sh D.γ₁ * paperFT D.kernel D.γ₁
  set Y₀ := polarSymbol sh D.γ₀ * paperFT (D.tailPart (a - 1 / 4)) D.γ₀
  set Y₁ := polarSymbol sh D.γ₁ * paperFT (D.tailPart (a - 1 / 4)) D.γ₁
  have hA : paperFT (D.test a) (gammaOf ρ₀) = X₀ - Y₀ := by
    rw [hγ, D.paperFT_test, D.nodeSymbol_γ₀]; ring
  have hB : paperFT (D.test a) (gammaOf ρ₁) = D.vval * (X₁ - Y₁) := by
    rw [hγ₁, D.paperFT_test, D.nodeSymbol_γ₁]; ring
  have hQ : X₀ * (starRingEnd ℂ) X₁ * (starRingEnd ℂ) D.vval =
      -(‖X₀ * (starRingEnd ℂ) X₁‖ : ℂ) := D.Qval_mul_conj_vval
  have hblock := re_node_block_le (Y₀ := Y₀) (Y₁ := Y₁) D.norm_vval hQ
  have hY₀ : ‖Y₀‖ ≤ ε' := by
    rw [norm_mul, hε']
    have := norm_polarSymbol_le sh_pos.le D.him2
    have := hEb _ D.him2
    gcongr
  have hY₁ : ‖Y₁‖ ≤ ε' := by
    rw [norm_mul, hε']
    have := norm_polarSymbol_le sh_pos.le D.him₁
    have := hEb _ D.him₁
    gcongr
  -- combine with the Hodge index
  have h0 := hH (D.test a) hC2 (D.tsupport_test a) (D.paperFT_test_half_I a)
    (D.paperFT_test_neg_half_I a)
  rw [hA, hB] at hsplit
  set M : ℝ := (zetaZeroConfig.mult ρ₀ : ℝ) + zetaZeroConfig.mult ρ₁ with hM
  have hM1 : 1 ≤ M := by
    have := zetaZeroConfig.one_le_mult ρ₀ hρ₀
    have : (1 : ℝ) ≤ zetaZeroConfig.mult ρ₀ := by exact_mod_cast this
    have : (0 : ℝ) ≤ zetaZeroConfig.mult ρ₁ := Nat.cast_nonneg _
    linarith
  set R : ℝ := (5 / 4) * zeroSumZ * ((CN * ε') * (Real.exp (a / 2) *
    (4 * ((∫ u, ‖D.test a u‖) + ∫ u, ‖deriv (deriv (D.test a)) u‖))))
  have hR0 : 0 ≤ R := by
    have := zeroSumZ_nonneg
    have h1 : 0 ≤ ∫ u, ‖D.test a u‖ := integral_nonneg fun _ => norm_nonneg _
    have h2 : 0 ≤ ∫ u, ‖deriv (deriv (D.test a)) u‖ := integral_nonneg fun _ => norm_nonneg _
    positivity
  set q : ℝ := -(‖X₀‖ * ‖X₁‖) + ‖X₀‖ * ‖Y₁‖ + ‖Y₀‖ * ‖X₁‖ + ‖Y₀‖ * ‖Y₁‖
  have hmain : 0 ≤ M * q + R := by
    have := mul_le_mul_of_nonneg_left hblock (by linarith : (0 : ℝ) ≤ M)
    linarith
  have hq : 0 ≤ q + R := by
    rcases le_or_gt 0 q with hq0 | hq0
    · linarith
    · nlinarith
  have hX0 : 0 ≤ ‖X₀‖ := norm_nonneg _
  have hX1 : 0 ≤ ‖X₁‖ := norm_nonneg _
  have t1 : ‖X₀‖ * ‖Y₁‖ ≤ ‖X₀‖ * ε' := mul_le_mul_of_nonneg_left hY₁ hX0
  have t2 : ‖Y₀‖ * ‖X₁‖ ≤ ε' * ‖X₁‖ := mul_le_mul_of_nonneg_right hY₀ hX1
  have t3 : ‖Y₀‖ * ‖Y₁‖ ≤ ε' * ε' := mul_le_mul hY₀ hY₁ (norm_nonneg _) hε'0
  nlinarith

/-! ### The flatness law -/

theorem norm_paperFT_kernel_le {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT D.kernel z‖ ≤ expTail D.kernel (1 / 2) 0 := by
  unfold paperFT expTail
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun u => norm_nonneg _)
    (D.superExpDecay_kernel.integrable_tail _ _) (Eventually.of_forall fun u => ?_))
  simp only [indicator, mem_setOf_eq, abs_nonneg, if_true]
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_cexp_I_mul_le_exp hz u) (norm_nonneg _)

theorem exp_sh_half_le : Real.exp (sh / 2) ≤ 3 / 2 := by
  have h : sh / 2 = 1 / 16 := by norm_num [sh]
  rw [h]
  have := Real.exp_bound' (x := 1 / 16) (by norm_num) (by norm_num) (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at this
  linarith

/-- The arithmetic of the flatness law. -/
theorem flatness_arith {X₀ X₁ e' N12 CN opF gN S Kp κ Γ Ea G εΦ t : ℝ}
    (hnode : X₀ * X₁ ≤ e' * (X₀ + X₁ + e') + (5 / 4) * S * ((CN * e') * (Ea * (4 * N12))))
    (hX₀ : X₀ ≤ 3 * (t * G)) (hX₁ : X₁ ≤ 3 * (t * G)) (hX₀0 : 0 ≤ X₀) (hX₁0 : 0 ≤ X₁)
    (he' : e' ≤ 3 * (t * εΦ)) (he'0 : 0 ≤ e') (hεG : εΦ ≤ G) (hεΦ0 : 0 ≤ εΦ)
    (hN12 : N12 ≤ 4 * Kp * opF * (Γ ^ 2 * gN)) (hN120 : 0 ≤ N12) (hgN : gN ≤ t * G)
    (hgN0 : 0 ≤ gN) (hCN : CN ≤ 24 * (1 + κ)) (hCN0 : 0 ≤ CN) (hopF : opF ≤ 50 * (1 + κ))
    (hS : 0 ≤ S) (hKp : 2 ≤ Kp) (hκ : 0 ≤ κ) (hΓ : 1 ≤ Γ) (hEa : 1 ≤ Ea)
    (ht : 0 ≤ t) :
    X₀ * X₁ ≤ (27 + 72000 * S * Kp) * t ^ 2 * (1 + κ) ^ 2 * Γ ^ 2 * Ea * εΦ * G := by
  have hG0 : 0 ≤ G := hεΦ0.trans hεG
  have hK0 : 0 ≤ Kp := by linarith
  have hB1 : 1 ≤ (1 + κ) ^ 2 * Γ ^ 2 * Ea := by
    have h1 : 1 ≤ (1 + κ) ^ 2 := by nlinarith
    have h2 : 1 ≤ Γ ^ 2 := by nlinarith
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ (1 + κ) ^ 2 * Γ ^ 2 * Ea := by gcongr
  have hT0 : 0 ≤ t ^ 2 * εΦ * G := by positivity
  have term1 : e' * (X₀ + X₁ + e') ≤ 27 * (t ^ 2 * εΦ * G) := by
    have hsum : X₀ + X₁ + e' ≤ 9 * (t * G) := by
      have : e' ≤ 3 * (t * G) := he'.trans (by gcongr)
      linarith
    calc e' * (X₀ + X₁ + e') ≤ (3 * (t * εΦ)) * (9 * (t * G)) :=
          mul_le_mul he' hsum (by positivity) (by positivity)
      _ = 27 * (t ^ 2 * εΦ * G) := by ring
  have term2 : (5 / 4) * S * ((CN * e') * (Ea * (4 * N12))) ≤
      72000 * S * Kp * ((1 + κ) ^ 2 * Γ ^ 2 * Ea) * (t ^ 2 * εΦ * G) := by
    have hN12' : N12 ≤ 4 * Kp * (50 * (1 + κ)) * (Γ ^ 2 * (t * G)) := by
      refine hN12.trans ?_
      gcongr
    calc (5 / 4) * S * ((CN * e') * (Ea * (4 * N12)))
        ≤ (5 / 4) * S * ((24 * (1 + κ) * (3 * (t * εΦ))) *
          (Ea * (4 * (4 * Kp * (50 * (1 + κ)) * (Γ ^ 2 * (t * G)))))) := by
          gcongr
      _ = 72000 * S * Kp * ((1 + κ) ^ 2 * Γ ^ 2 * Ea) * (t ^ 2 * εΦ * G) := by ring
  have h27 : 27 * (t ^ 2 * εΦ * G) ≤ 27 * ((1 + κ) ^ 2 * Γ ^ 2 * Ea) * (t ^ 2 * εΦ * G) := by
    have := mul_le_mul_of_nonneg_right hB1 hT0
    linarith
  calc X₀ * X₁ ≤ 27 * (t ^ 2 * εΦ * G) +
        72000 * S * Kp * ((1 + κ) ^ 2 * Γ ^ 2 * Ea) * (t ^ 2 * εΦ * G) :=
        hnode.trans (add_le_add term1 term2)
    _ ≤ (27 + 72000 * S * Kp) * t ^ 2 * (1 + κ) ^ 2 * Γ ^ 2 * Ea * εΦ * G := by nlinarith

/-- **Flatness law at an off-line pair.** There is an absolute constant `C` such that, if the
level-`a` Hodge index holds (`a ≥ 1`), then for the node values `X_j = P(γ_j) ĥ(γ_j)` of any
off-line zero,
`|X₀||X₁| ≤ C 4^n (1 + 1/|Im γ₀|)² (1+|γ₀|)² e^{a/2} · ε_Φ(a) · G_Φ`,
with `ε_Φ(a) = ∫_{|u| ≥ a-3/8} ‖Φ‖ e^{(1/2+3n/2)|u|}` the tail of Riemann's kernel and
`G_Φ = ∫ ‖Φ‖ e^{(1/2+3n/2)|u|}`. -/
theorem flatness :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : OffLinePairData) {ρ₀ : ℂ}, ρ₀ ∈ zetaZeroConfig.carrier →
      gammaOf ρ₀ = D.γ₀ → ∀ {a : ℝ}, 1 ≤ a → HodgeIndexAtLevel zetaZeroConfig a →
        ‖polarSymbol sh D.γ₀ * paperFT D.kernel D.γ₀‖ *
            ‖polarSymbol sh D.γ₁ * paperFT D.kernel D.γ₁‖ ≤
          C * (2 ^ D.n) ^ 2 * (1 + 1 / |D.γ₀.im|) ^ 2 * (1 + ‖D.γ₀‖) ^ 2 * Real.exp (a / 2) *
            expTail Φ (1 / 2 + 3 / 2 * D.n) (a - 1 / 4 - sh) *
            expTail Φ (1 / 2 + 3 / 2 * D.n) 0 := by
  obtain ⟨Kp, hKp2, hKp⟩ := exists_plateau_constant
  have hS := zeroSumZ_nonneg
  refine ⟨27 + 72000 * zeroSumZ * Kp, by positivity, fun D ρ₀ hρ₀ hγ a ha hH => ?_⟩
  have hnode := D.node_inequality hρ₀ hγ (by linarith) hH
  obtain ⟨-, hnorm⟩ := D.test_calculus a hKp2 hKp
  have hsh : sh = 1 / 8 := rfl
  have hexp := exp_sh_half_le
  have hH0 : expTail D.kernel (1 / 2) 0 ≤ 2 ^ D.n * expTail Φ (1 / 2 + 3 / 2 * D.n) 0 :=
    D.expTail_kernel_le (by norm_num)
  have hX : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖polarSymbol sh z * paperFT D.kernel z‖ ≤
      3 * (2 ^ D.n * expTail Φ (1 / 2 + 3 / 2 * D.n) 0) := by
    intro z hz
    rw [norm_mul]
    have h1 := norm_polarSymbol_le sh_pos.le hz
    have h2 := (D.norm_paperFT_kernel_le hz).trans hH0
    have h3 : 0 ≤ 2 ^ D.n * expTail Φ (1 / 2 + 3 / 2 * D.n) 0 :=
      mul_nonneg (by positivity) (expTail_nonneg _ _ _)
    calc ‖polarSymbol sh z‖ * ‖paperFT D.kernel z‖ ≤
          (2 * Real.exp (sh / 2)) * (2 ^ D.n * expTail Φ (1 / 2 + 3 / 2 * D.n) 0) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ ≤ 3 * (2 ^ D.n * expTail Φ (1 / 2 + 3 / 2 * D.n) 0) := by gcongr; linarith
  have hε : D.tailSize a ≤ 2 ^ D.n * expTail Φ (1 / 2 + 3 / 2 * D.n) (a - 1 / 4 - sh) :=
    D.expTail_kernel_le (by norm_num)
  have hε' : 2 * Real.exp (sh / 2) * D.tailSize a ≤
      3 * (2 ^ D.n * expTail Φ (1 / 2 + 3 / 2 * D.n) (a - 1 / 4 - sh)) := by
    have := expTail_nonneg D.kernel (1 / 2) (a - 1 / 4 - sh)
    calc 2 * Real.exp (sh / 2) * D.tailSize a ≤ 3 * D.tailSize a := by gcongr; linarith
      _ ≤ _ := by gcongr
  have hc₂ : ‖D.c₂‖ ≤ 8 * (1 / |D.γ₀.im|) := by
    have := D.norm_c₂_le; rw [hsh] at this
    calc ‖D.c₂‖ ≤ 1 / (1 / 8 * |D.γ₀.im|) := this
      _ = 8 * (1 / |D.γ₀.im|) := by field_simp
  have hκ0 : 0 ≤ 1 / |D.γ₀.im| := by positivity
  have hc₁ : ‖D.c₁‖ ≤ 1 + 12 * (1 / |D.γ₀.im|) := by
    have h := D.norm_c₁_le
    have e : Real.exp (sh / 2) / (sh * |D.γ₀.im|) = Real.exp (sh / 2) * (8 * (1 / |D.γ₀.im|)) := by
      rw [hsh]; field_simp
    rw [e] at h
    have := mul_le_mul_of_nonneg_right hexp (by positivity : (0 : ℝ) ≤ 8 * (1 / |D.γ₀.im|))
    linarith
  have hCN : ‖D.c₁‖ + ‖D.c₂‖ * Real.exp (sh / 2) ≤ 24 * (1 + 1 / |D.γ₀.im|) := by
    have := mul_le_mul hc₂ hexp (Real.exp_pos _).le (by positivity)
    linarith
  have hopF : D.opFactor ≤ 50 * (1 + 1 / |D.γ₀.im|) := by
    unfold opFactor
    have hc : Real.cosh (sh / 2) ≤ 3 / 2 := by
      have := cosh_le_exp_abs (sh / 2)
      rw [abs_of_pos (by rw [hsh]; norm_num)] at this; linarith
    have : ‖D.c₁‖ + ‖D.c₂‖ ≤ 20 * (1 + 1 / |D.γ₀.im|) := by linarith
    calc (‖D.c₁‖ + ‖D.c₂‖) * (1 + Real.cosh (sh / 2)) ≤ (20 * (1 + 1 / |D.γ₀.im|)) * (5 / 2) := by
          gcongr; linarith
      _ = 50 * (1 + 1 / |D.γ₀.im|) := by ring
  have hgN : D.gNorm ≤ 2 ^ D.n * expTail Φ (1 / 2 + 3 / 2 * D.n) 0 := by
    unfold gNorm
    exact mul_le_mul_of_nonneg_left (expTail_mono_weight superExpDecay_riemannPhiKernel
      (by linarith) 0) (by positivity)
  have hN120 : 0 ≤ (∫ u, ‖D.test a u‖) + ∫ u, ‖deriv (deriv (D.test a)) u‖ := by
    have h1 : 0 ≤ ∫ u, ‖D.test a u‖ := integral_nonneg fun _ => norm_nonneg _
    have h2 : 0 ≤ ∫ u, ‖deriv (deriv (D.test a)) u‖ := integral_nonneg fun _ => norm_nonneg _
    positivity
  have he'0 : 0 ≤ 2 * Real.exp (sh / 2) * D.tailSize a := by
    have := expTail_nonneg D.kernel (1 / 2) (a - 1 / 4 - sh); positivity
  have hεG : expTail Φ (1 / 2 + 3 / 2 * D.n) (a - 1 / 4 - sh) ≤
      expTail Φ (1 / 2 + 3 / 2 * D.n) 0 :=
    expTail_anti superExpDecay_riemannPhiKernel _ (by rw [hsh]; linarith)
  exact flatness_arith hnode (hX _ D.him2) (hX _ D.him₁) (norm_nonneg _) (norm_nonneg _) hε' he'0
    hεG (expTail_nonneg _ _ _) hnorm hN120 hgN D.gNorm_nonneg hCN (by positivity) hopF
    hS hKp2 hκ0 (by linarith [norm_nonneg D.γ₀])
    (Real.one_le_exp (by linarith)) (by positivity)

/-- Every off-line zero carries detection data at `γ₀ = gammaOf ρ₀`. -/
theorem exists_offLinePairData {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier)
    (hoff : ρ₀.re ≠ 1 / 2) : ∃ D : OffLinePairData, D.γ₀ = gammaOf ρ₀ := by
  have h0 : riemannXiHat (gammaOf ρ₀) = 0 := riemannXiHat_gammaOf_eq_zero hρ₀
  have h1 : riemannXiHat ((starRingEnd ℂ) (gammaOf ρ₀)) = 0 := by
    rw [← gammaOf_reflect']
    exact riemannXiHat_gammaOf_eq_zero (zetaZeroConfig.reflect_mem ρ₀ hρ₀)
  obtain ⟨m₀, u₀, hm₀, hu₀, hu₀0, hloc₀⟩ := exists_local_factor_riemannXiHat h0
  obtain ⟨m₁, u₁, hm₁, hu₁, hu₁0, hloc₁⟩ := exists_local_factor_riemannXiHat h1
  have hstrip : 0 < ρ₀.re ∧ ρ₀.re < 1 := by
    have h : IsNontrivialZero ρ₀ := hρ₀
    exact ⟨h.2.1, h.2.2⟩
  have him : (gammaOf ρ₀).im ≠ 0 := by
    rw [WeilEF.gammaOf_im]; intro h; exact hoff (by linarith)
  exact ⟨⟨gammaOf ρ₀, m₀, m₁, u₀, u₁, hm₀, hm₁, hu₀, hu₁, hu₀0, hu₁0, hloc₀, hloc₁, him,
    (WeilEF.abs_gammaOf_im_lt hstrip).le⟩, rfl⟩

end OffLinePairData

end

end RHTower
