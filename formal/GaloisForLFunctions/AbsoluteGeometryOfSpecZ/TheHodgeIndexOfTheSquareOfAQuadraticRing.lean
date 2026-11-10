import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheSquareOfAQuadraticRingPairsWithItsConductor
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheHodgeIndexOfThePairingOfTheDegreePoints
import GaloisForLFunctions.RHTower.DirichletArchimedeanSymbolPositivity

/-!
# The Hodge index of the square of a quadratic ring

For a primitive character `χ` of conductor `q > 1` the pairing with the contacts `Λ(1 + Re χ)`,
for a real `χ` the pairing of the square of its quadratic ring counted by norms, has on a packet
the limit `2 d₁ d₂ − Z_ζ(f) − Z_χ(f)`. On a finite family
of packets both zero sums are quadratic forms, and the index law of a tempered configuration
(corpus) reads on the ring.

* **The pairing on a family of packets** (`twistedZeroSum_packetCombination`,
  `tendsto_quadraticPairing_packetCombination`): the limit on a combination `Σ x_i f_i` is
  `2 d₁ d₂` minus the quadratic form of the sum of the two Gram matrices of the zeros.
* **The index law** (`negIndex_quadraticDefect_packets_le`): the defect `2 d₁ d₂ − D·D` has at
  most as many negative squares as `ζ` and `L(s, χ)` together have zeros to the right of the
  critical line. The twisted part, which has no pole plane, has at most as many positive squares
  as `L(s, χ)` has such zeros (`negIndex_twistedGram_packets_le`).
* **Short packets** (`twistedZeroSum_nonneg_of_level`, `twistedZeroSum_nonneg_of_short`,
  `tendsto_quadraticForm_le_degrees_of_short`): a packet shorter than `log 2` meets no contact.
  For an odd character of conductor `q ≥ 4π` and an even one of conductor `q ≥ 128π` the
  twisted part is then nonpositive, and the inequality of Castelnuovo and Severi holds on the
  square of the ring with the margin `∫f²/5000`. The conductor, the density of the comb of the
  twisted part, exceeds the archimedean constant.

So the square of a quadratic ring has the Hodge index of its zeta function on packets, with the
same bound by the zeros to the right of the line as the square of `ℤ`, and the inequality is a
theorem where no contact enters, once the conductor is large.
-/

open Finset Filter Topology MeasureTheory Matrix
open scoped ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry
open scoped ArithmeticFunction.vonMangoldt Real

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

variable {ι : Type*} [Fintype ι] {q : ℕ}

/-! ### The pairing on a family of packets -/

/-- The zeros of `L(s, χ)` in the critical strip form a tempered configuration. -/
theorem temperedConfig_dirichletZeros [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) :
    SquareRootThreshold.TemperedConfig (_root_.RHTower.dirichletZeros hq hprim) :=
  _root_.RHTower.summable_dirichletZeros hq hprim

/-- The sum over the zeros of `L(s, χ)` of a combination of packets is the quadratic form of the
Gram matrix of the zeros on the family. -/
theorem twistedZeroSum_packetCombination [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) {f : ι → ℝ → ℝ} (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) (x : ι → ℝ) :
    twistedZeroSum hq hprim (packetCombination f x) =
      hermQuad (ArithmeticCastelnuovoSeveri.zeroGram (_root_.RHTower.dirichletZeros hq hprim)
        fun i u => ((f i u : ℝ) : ℂ)) (fun i => ((x i : ℝ) : ℂ)) := by
  rw [ArithmeticCastelnuovoSeveri.hermQuad_zeroGram_of_tempered _
      (temperedConfig_dirichletZeros hq hprim) _
      (fun i => contDiff_ofReal_packet (hf i)) (fun i => hasCompactSupport_ofReal_packet (hfc i)),
    twistedZeroSum, ofReal_packetCombination]

/-- **The pairing of the square of a quadratic ring on a combination of packets**: twice the
product of the degrees minus the quadratic form of the two Gram matrices of the zeros. -/
theorem tendsto_quadraticPairing_packetCombination [NeZero q] (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) {f : ι → ℝ → ℝ} (hf : ∀ i, ContDiff ℝ 2 (f i)) (hfc : ∀ i, HasCompactSupport (f i))
    {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ i u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f i u = 0) (x : ι → ℝ) :
    Tendsto (fun N : ℕ => quadraticForm χ (packetCombination f x) (3 * K) N +
        2 * weightedContact (idealWeight χ) (packetCombination f x) (3 * K) N) atTop
      (𝓝 (2 * ((∫ u, packetCombination f x u * Real.exp (-u / 2)) *
            ∫ u, packetCombination f x u * Real.exp (u / 2)) -
          hermQuad (ArithmeticCastelnuovoSeveri.weilGram (fun n => (Λ n : ℝ))
              (fun i u => ((f i u : ℝ) : ℂ)) +
            ArithmeticCastelnuovoSeveri.zeroGram (_root_.RHTower.dirichletZeros hq hprim)
              fun i u => ((f i u : ℝ) : ℂ)) (fun i => ((x i : ℝ) : ℂ)))) := by
  have hs : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → packetCombination f x u = 0 := fun u hu =>
    Finset.sum_eq_zero fun i _ => by rw [hsupp i u hu, mul_zero]
  have h := tendsto_quadraticForm_add_idealContact hq hprim
    (contDiff_packetCombination hf x) (hasCompactSupport_packetCombination hfc x) hK hs
  rwa [zeroSum_packetCombination hf hfc x, twistedZeroSum_packetCombination hq hprim hf hfc x,
    ← hermQuad_add] at h

/-! ### The index law -/

/-- Weil's form of a tempered configuration is nonnegative on the combinations of a family whose
transforms vanish at the zeros to the right of the line. -/
theorem hermQuad_zeroGram_nonneg_of_vanish (Z : ZeroConfig)
    (hZ : SquareRootThreshold.TemperedConfig Z) (F : ι → ℝ → ℂ) (hF : ∀ i, ContDiff ℝ 2 (F i))
    (hFc : ∀ i, HasCompactSupport (F i)) (x : ι → ℂ)
    (hx : ∀ ρ ∈ Z.carrier, 1 / 2 < ρ.re →
      ArithmeticCastelnuovoSeveri.evalFunctional F (gammaOf ρ) x = 0) :
    0 ≤ hermQuad (ArithmeticCastelnuovoSeveri.zeroGram Z F) x := by
  have hFv : ∀ ρ ∈ Z.carrier, 1 / 2 < ρ.re →
      paperFT (∑ i, conj (x i) • F i) (gammaOf ρ) = 0 := by
    intro ρ hρ hre
    have := hx ρ hρ hre
    rw [ArithmeticCastelnuovoSeveri.evalFunctional_eq F (fun i => (hF i).continuous) hFc] at this
    simpa using this
  have hFd := ArithmeticCastelnuovoSeveri.contDiff_sum_smul F hF fun i => conj (x i)
  have hFc' := ArithmeticCastelnuovoSeveri.hasCompactSupport_sum_smul F hFc fun i => conj (x i)
  rw [ArithmeticCastelnuovoSeveri.hermQuad_zeroGram_of_tempered Z hZ F hF hFc, ZeroConfig.W,
    Complex.re_tsum (ArithmeticCastelnuovoSeveri.summable_Wsummand Z hZ hFd hFc' hFd hFc')]
  exact tsum_nonneg fun ρ => ArithmeticCastelnuovoSeveri.re_Wsummand_nonneg Z hFv ρ

/-- **The twisted part has few positive squares.** On every finite family of packets the Gram
matrix of the zeros of `L(s, χ)`, minus the twisted part of the pairing, has at most as many
negative squares as `L(s, χ)` has zeros to the right of the critical line. -/
theorem negIndex_twistedGram_packets_le [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) {f : ι → ℝ → ℝ} (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) :
    (hermNegIndex (ArithmeticCastelnuovoSeveri.zeroGram (_root_.RHTower.dirichletZeros hq hprim)
        fun i u => ((f i u : ℝ) : ℂ)) : ℕ∞) ≤
      (ArithmeticCastelnuovoSeveri.rightZeros (_root_.RHTower.dirichletZeros hq hprim)).encard :=
  ArithmeticCastelnuovoSeveri.negIndex_zeroGram_le_of_tempered _
    (temperedConfig_dirichletZeros hq hprim) _
    (fun i => contDiff_ofReal_packet (hf i)) (fun i => hasCompactSupport_ofReal_packet (hfc i))

/-- **The index law on the square of a quadratic ring.** On every finite family of packets the
defect `2 d₁ d₂ − D·D` of the pairing has at most as many negative squares as `ζ` and `L(s, χ)`
together have zeros to the right of the critical line. -/
theorem negIndex_quadraticDefect_packets_le [NeZero q] (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) {f : ι → ℝ → ℝ}
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hfc : ∀ i, HasCompactSupport (f i)) :
    (hermNegIndex (ArithmeticCastelnuovoSeveri.weilGram (fun n => (Λ n : ℝ))
          (fun i u => ((f i u : ℝ) : ℂ)) +
        ArithmeticCastelnuovoSeveri.zeroGram (_root_.RHTower.dirichletZeros hq hprim)
          fun i u => ((f i u : ℝ) : ℂ)) : ℕ∞) ≤
      (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard +
        (ArithmeticCastelnuovoSeveri.rightZeros
          (_root_.RHTower.dirichletZeros hq hprim)).encard := by
  classical
  have hF : ∀ i, ContDiff ℝ 2 fun u => ((f i u : ℝ) : ℂ) := fun i =>
    contDiff_ofReal_packet (hf i)
  have hFc : ∀ i, HasCompactSupport fun u => ((f i u : ℝ) : ℂ) := fun i =>
    hasCompactSupport_ofReal_packet (hfc i)
  rw [ArithmeticCastelnuovoSeveri.weilGram_eq_zeroGram _ hF hFc]
  rcases (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).finite_or_infinite with h1 | h1
  · rcases (ArithmeticCastelnuovoSeveri.rightZeros
        (_root_.RHTower.dirichletZeros hq hprim)).finite_or_infinite with h2 | h2
    · haveI := h1.fintype
      haveI := h2.fintype
      rw [h1.encard_eq_coe_toFinset_card, h2.encard_eq_coe_toFinset_card,
        Set.Finite.card_toFinset, Set.Finite.card_toFinset, ← Nat.cast_add,
        ← Fintype.card_sum]
      refine ENat.coe_le_coe.mpr (ArithmeticCastelnuovoSeveri.negIndex_le_card_of_nonneg_on_ker _
        (Sum.elim
          (fun ρ : ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig =>
            ArithmeticCastelnuovoSeveri.evalFunctional (fun i u => ((f i u : ℝ) : ℂ))
              (gammaOf ρ))
          (fun ρ : ArithmeticCastelnuovoSeveri.rightZeros
              (_root_.RHTower.dirichletZeros hq hprim) =>
            ArithmeticCastelnuovoSeveri.evalFunctional (fun i u => ((f i u : ℝ) : ℂ))
              (gammaOf ρ))) fun x hx => ?_)
      rw [hermQuad_add]
      exact add_nonneg
        (hermQuad_zeroGram_nonneg_of_vanish _ SquareRootThreshold.temperedConfig_zetaZeroConfig
          _ hF hFc x fun ρ hρ hre => hx (Sum.inl ⟨ρ, hρ, hre⟩))
        (hermQuad_zeroGram_nonneg_of_vanish _ (temperedConfig_dirichletZeros hq hprim)
          _ hF hFc x fun ρ hρ hre => hx (Sum.inr ⟨ρ, hρ, hre⟩))
    · rw [h2.encard_eq, add_top]
      exact le_top
  · rw [h1.encard_eq, top_add]
    exact le_top

/-! ### Short packets -/

/-- **A packet too short for a contact and a large conductor.** For an odd primitive character
of conductor `q ≥ 4π`, or an even one of conductor `q ≥ 128π`, the sum over the zeros of
`L(s, χ)` is nonnegative on every packet supported in `[−a, a]` with `2a < log 2`. -/
theorem twistedZeroSum_nonneg_of_level [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hlarge : (χ.Odd ∧ 4 * π ≤ q) ∨ (χ.Even ∧ 128 * π ≤ q)) {a : ℝ}
    (ha0 : 0 ≤ a) (ha : 2 * a < Real.log 2) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hGs : tsupport (fun u => (g u : ℂ)) ⊆ Set.Icc (-a) a) :
    0 ≤ twistedZeroSum hq hprim g := by
  have hG := contDiff_ofReal_packet hg
  have hN : ⌊Real.exp (2 * a)⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (Real.exp_pos _).le]
    have h2 : Real.exp (2 * a) < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr ha
    rw [Real.exp_log two_pos] at h2
    refine ⟨by simpa using Real.one_le_exp (by linarith : 0 ≤ 2 * a), ?_⟩
    norm_num
    exact h2
  have hsymb : ∀ (w : ℕ → ℝ) (ξ : ℝ), _root_.RHTower.weilAtomSymbol w 1 ξ =
      _root_.RHTower.weilAtomSymbol (fun _ => 0) 0 ξ := fun w ξ => by
    simp [_root_.RHTower.weilAtomSymbol]
  have hπ : 0 < π := Real.pi_pos
  have hh : Integrable fun τ : ℝ => ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 :=
    _root_.RHTower.integrable_normSq_paperFT hG hGs
  have hS : Integrable fun τ : ℝ => ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
      _root_.RHTower.weilAtomSymbol (twistWeight χ) 1 (τ / (2 * π)) := by
    have := _root_.RHTower.integrable_normSq_paperFT_mul_weilAtomSymbol_of hG hGs (twistWeight χ)
    rwa [hN] at this
  have hB : Integrable fun τ : ℝ => Real.log q * ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 :=
    hh.const_mul _
  have hAB : Integrable fun τ : ℝ => ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
      _root_.RHTower.weilAtomSymbol (twistWeight χ) 1 (τ / (2 * π)) +
        Real.log q * ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 := hS.add hB
  have hform := integral_weilAtomSymbol_twist_packet hq hprim hg hGs
  rw [hN] at hform
  rcases hlarge with ⟨hodd, hq4⟩ | ⟨heven, hq128⟩
  · have hpos := _root_.RHTower.integral_oddDirichletArchSymbol_nonneg hq4
      (fun u => (g u : ℂ))
    have hC : Integrable fun τ : ℝ => ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
        (π / Real.cosh (π * τ)) := by
      have hGc : HasCompactSupport fun u => (g u : ℂ) :=
        IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hGs
      have hhc : Continuous fun τ : ℝ => ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 :=
        _root_.RHTower.BlindPrimePowerSlack.continuous_normSq_paperFT ⟨_, hG, hGc⟩
      refine (hh.const_mul π).mono' (hhc.mul (continuous_const.div
        (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
        fun τ => (Real.cosh_pos _).ne')).aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
      show ‖‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 * (π / Real.cosh (π * τ))‖ ≤
        π * ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2
      have hc : 1 ≤ Real.cosh (π * τ) := Real.one_le_cosh _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
        (div_nonneg hπ.le (by linarith))), mul_comm]
      exact mul_le_mul_of_nonneg_right (div_le_self hπ.le hc) (sq_nonneg _)
    have hsplit : ∫ τ : ℝ, ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
          (_root_.RHTower.weilAtomSymbol (fun _ => 0) 0 (τ / (2 * π)) + Real.log q +
            π / Real.cosh (π * τ)) =
        (∫ τ : ℝ, ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
          _root_.RHTower.weilAtomSymbol (twistWeight χ) 1 (τ / (2 * π))) +
          Real.log q * (∫ τ : ℝ, ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2) +
          ∫ τ : ℝ, ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 * (π / Real.cosh (π * τ)) := by
      rw [← integral_const_mul, ← integral_add hS hB, ← integral_add hAB hC]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      show ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
          (_root_.RHTower.weilAtomSymbol (fun _ => 0) 0 (τ / (2 * π)) + Real.log q +
            π / Real.cosh (π * τ)) =
        ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
            _root_.RHTower.weilAtomSymbol (twistWeight χ) 1 (τ / (2 * π)) +
          Real.log q * ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 +
          ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 * (π / Real.cosh (π * τ))
      rw [hsymb]
      ring
    rw [hsplit, hform, placeEnergy_of_odd hodd] at hpos
    have hcancel : 2 * π * (1 / (2 * π) * ∫ τ : ℝ, ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
          (π / Real.cosh (π * τ))) =
        ∫ τ : ℝ, ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 * (π / Real.cosh (π * τ)) := by
      field_simp
    rw [hcancel] at hpos
    nlinarith
  · have hpos := _root_.RHTower.integral_evenDirichletArchSymbol_nonneg hq128
      (fun u => (g u : ℂ))
    have hsplit : ∫ τ : ℝ, ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
          (_root_.RHTower.weilAtomSymbol (fun _ => 0) 0 (τ / (2 * π)) + Real.log q) =
        (∫ τ : ℝ, ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
          _root_.RHTower.weilAtomSymbol (twistWeight χ) 1 (τ / (2 * π))) +
          Real.log q * ∫ τ : ℝ, ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 := by
      rw [← integral_const_mul, ← integral_add hS hB]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      show ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
          (_root_.RHTower.weilAtomSymbol (fun _ => 0) 0 (τ / (2 * π)) + Real.log q) =
        ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2 *
            _root_.RHTower.weilAtomSymbol (twistWeight χ) 1 (τ / (2 * π)) +
          Real.log q * ‖paperFT (fun u => (g u : ℂ)) τ‖ ^ 2
      rw [hsymb]
      ring
    rw [hsplit, hform, placeEnergy_of_even heven] at hpos
    nlinarith

variable {f : ℝ → ℝ}

/-- On a packet shorter than `log 2` the zero sum of `L(s, χ)` is nonnegative, for a large
conductor. -/
theorem twistedZeroSum_nonneg_of_short [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hlarge : (χ.Odd ∧ 4 * π ≤ q) ∨ (χ.Even ∧ 128 * π ≤ q)) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {c a : ℝ} (ha0 : 0 ≤ a) (ha : 2 * a < Real.log 2)
    (hshort : ∀ u, a < |u - c| → f u = 0) :
    0 ≤ twistedZeroSum hq hprim f := by
  have hg : ContDiff ℝ 2 fun u => f (u - -c) := hf.comp (contDiff_id.sub contDiff_const)
  have hg0 : ∀ x : ℝ, a < |x| → f (x - -c) = 0 := fun x hx =>
    hshort _ (by rwa [sub_neg_eq_add, add_sub_cancel_right])
  have hts : tsupport (fun x => ((f (x - -c) : ℝ) : ℂ)) ⊆ Set.Icc (-a) a := by
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
  rw [← twistedZeroSum_translate hq hprim hf hfc (-c)]
  exact twistedZeroSum_nonneg_of_level hq hprim hlarge ha0 ha hg hts

/-- **The inequality of Castelnuovo and Severi on the square of a quadratic ring, where no contact
enters.** For an odd character of conductor `q ≥ 4π` or an even one of conductor `q ≥ 128π`, and
a packet shorter than `log 2`: the pairing of the ring has a limit, at most twice the product of
the degrees minus `∫ f²/5000`. -/
theorem tendsto_quadraticForm_le_degrees_of_short [NeZero q] (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hlarge : (χ.Odd ∧ 4 * π ≤ q) ∨ (χ.Even ∧ 128 * π ≤ q)) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) {c a : ℝ} (ha0 : 0 ≤ a)
    (ha : 2 * a < Real.log 2) (hshort : ∀ u, a < |u - c| → f u = 0) :
    ∃ l : ℝ, Tendsto (fun N : ℕ => quadraticForm χ f (3 * K) N +
          2 * weightedContact (idealWeight χ) f (3 * K) N) atTop (𝓝 l) ∧
      l ≤ 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
        1 / 5000 * ∫ u, f u ^ 2 := by
  refine ⟨_, tendsto_quadraticForm_add_idealContact hq hprim hf hfc hK hsupp, ?_⟩
  have h1 := zeroSum_ge_of_width hf hfc (c := c) fun u hu => hshort u (by
    have := Real.log_two_lt_d9
    linarith)
  have h2 := twistedZeroSum_nonneg_of_short hq hprim hlarge hf hfc ha0 ha hshort
  linarith

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
