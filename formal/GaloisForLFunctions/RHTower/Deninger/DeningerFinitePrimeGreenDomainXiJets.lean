import GaloisForLFunctions.RHTower.Deninger.DeningerStrongLogEulerGreenTransport
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerFiniteXiJetPacket
import GaloisForLFunctions.RHTower.Deninger.DeningerAdiabaticGaussianBoundaryParity
import GaloisForLFunctions.RHTower.Deninger.DeningerTomographyInjective

/-!
# Finite prime Green domains and complete Xi jets

Each positive-period Euler defect is invertible on every full finite Xi jet
packet. Literal finite depletion consequently realizes every prescribed packet
inside all selected Green domains. Simultaneous admission at infinitely many
primes instead forces the entire original source to vanish.

Pairing a defect with its weighted-reflection mate preserves collar exchange.
Its exact strip multiplier never vanishes, and every leading Mellin derivative
retains that multiplier. Applying the finite paired product to the explicit
reflected Gaussian yields an admitted, collar-fixed source with nonzero Xi
values and a nonzero complete Gamma/flux boundary. Finite Green admission and
collar symmetry therefore supply no such cancellation.
-/

open Complex
open scoped Classical
namespace RHTower
noncomputable section


/-- The Euler defect on the complete finite Xi jet packet. -/
def deningerFiniteXiJetEulerDefect (S : Finset XiDivisorSupport) (L : ℝ) :
    DeningerMeyerFiniteXiJetPacket S →ₗ[ℂ] DeningerMeyerFiniteXiJetPacket S :=
  LinearMap.id - deningerMeyerFiniteXiJetPacketFlow S (-L)

/-- Every diagonal coefficient is nonzero at the unchanged Xi coordinate. -/
theorem deningerEulerXiCharacter_ne_one {L : ℝ} (hL : 0 < L)
    (rho : XiDivisorSupport) :
    Complex.exp ((-L : ℝ) * (rho : ℂ)) ≠ 1 := by
  intro h
  have hn := congrArg norm h
  rw [Complex.norm_exp, norm_one] at hn
  have hz : (↑(-L) * (rho : ℂ)).re = 0 := Real.exp_injective (hn.trans Real.exp_zero.symm)
  have hp := (xi_divisor_support_re_mem_open_unit rho).1
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hz
  have hneg : -L * (rho : ℂ).re < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos hL) hp
  linarith

/-- The full triangular defect is injective, including all confluent coordinates. -/
theorem deningerFiniteXiJetEulerDefect_injective (S : Finset XiDivisorSupport)
    {L : ℝ} (hL : 0 < L) : Function.Injective (deningerFiniteXiJetEulerDefect S L) := by
  apply (injective_iff_map_eq_zero _).2
  intro x hx
  have hcoord (rho : ↥S) : ∀ (k : ℕ) (hk : k < xiSupportMultiplicity rho.1),
      x ⟨rho, ⟨k, hk⟩⟩ = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      have heq := congrFun hx ⟨rho, ⟨k, hk⟩⟩
      change x ⟨rho, ⟨k, hk⟩⟩ -
        (∑ i ∈ Finset.range (k + 1), (k.choose i : ℂ) * ((-L : ℝ) : ℂ) ^ i *
          Complex.exp (((-L : ℝ) : ℂ) * (rho.1 : ℂ)) *
          x ⟨rho, ⟨k - i, lt_of_le_of_lt (Nat.sub_le k i) hk⟩⟩) = 0 at heq
      rw [Finset.sum_eq_single 0] at heq
      · simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul,
          Nat.sub_zero] at heq
        have hm : (1 - Complex.exp (((-L : ℝ) : ℂ) * (rho.1 : ℂ))) *
            x ⟨rho, ⟨k, hk⟩⟩ = 0 := by linear_combination heq
        exact (mul_eq_zero.mp hm).resolve_left
          (sub_ne_zero.mpr (Ne.symm (deningerEulerXiCharacter_ne_one hL rho.1)))
      · intro i hi hi0
        have hi' : i < k + 1 := Finset.mem_range.mp hi
        rw [ih (k-i) (by omega)]
        simp
      · simp
  funext q
  exact hcoord q.1 q.2.val q.2.isLt

/-- Finite Xi packets admit an exact inverse to each positive-period Euler defect. -/
theorem deningerFiniteXiJetEulerDefect_bijective (S : Finset XiDivisorSupport)
    {L : ℝ} (hL : 0 < L) : Function.Bijective (deningerFiniteXiJetEulerDefect S L) :=
  ⟨deningerFiniteXiJetEulerDefect_injective S hL,
    LinearMap.injective_iff_surjective.mp (deningerFiniteXiJetEulerDefect_injective S hL)⟩

/-- Finite depletion retains the order and repetitions of the original periods. -/
def deningerStrongLogFiniteDepletion : List ℝ →
    DeningerMeyerStrongLogTarget →ₗ[ℂ] DeningerMeyerStrongLogTarget
  | [] => LinearMap.id
  | L :: P => (deningerStrongLogDefect L).comp (deningerStrongLogFiniteDepletion P)

/-- Literal source and complete finite-jet Euler defects intertwine. -/
theorem deningerFiniteXiJetPacket_defect (S : Finset XiDivisorSupport) (L : ℝ)
    (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerFiniteXiJetPacketLM S (Submodule.Quotient.mk (deningerStrongLogDefect L g)) =
      deningerFiniteXiJetEulerDefect S L
        (deningerMeyerFiniteXiJetPacketLM S (Submodule.Quotient.mk g)) := by
  rw [deningerStrongLogDefect, LinearMap.sub_apply, LinearMap.id_apply,
    Submodule.Quotient.mk_sub, map_sub, ← deningerMeyerStrongLogCohomologyFlow_mk,
    deningerMeyerFiniteXiJetPacketLM_flow]
  rfl

/-- Finite depletion is still surjective on every full finite Xi jet packet. -/
theorem deningerStrongLogFiniteDepletion_jet_surjective
    (S : Finset XiDivisorSupport) (P : List ℝ) (hP : ∀ L ∈ P, 0 < L) :
    Function.Surjective (fun g : DeningerMeyerStrongLogTarget =>
      deningerMeyerFiniteXiJetPacketLM S
        (Submodule.Quotient.mk (deningerStrongLogFiniteDepletion P g))) := by
  induction P with
  | nil =>
      intro v
      obtain ⟨u, hu⟩ := deningerMeyerFiniteXiJetPacketLM_surjective S v
      obtain ⟨g, hg⟩ := Submodule.mkQ_surjective (LinearMap.range deningerMeyerStrongLogSumLM) u
      change Submodule.Quotient.mk g = u at hg
      refine ⟨g, ?_⟩
      change deningerMeyerFiniteXiJetPacketLM S (Submodule.Quotient.mk g) = v
      rw [hg, hu]
  | cons L P ih =>
      intro v
      obtain ⟨w, hw⟩ := (deningerFiniteXiJetEulerDefect_bijective S (hP L (by simp))).2 v
      obtain ⟨g, hg⟩ := ih (fun a ha => hP a (by simp [ha])) w
      refine ⟨g, ?_⟩
      change deningerMeyerFiniteXiJetPacketLM S
        (Submodule.Quotient.mk (deningerStrongLogDefect L (deningerStrongLogFiniteDepletion P g))) = v
      dsimp only at hg
      rw [deningerFiniteXiJetPacket_defect, hg, hw]

/-- The Euler factors commute on the literal source. -/
theorem deningerStrongLogDefect_comm (L M : ℝ) (g : DeningerMeyerStrongLogTarget) :
    deningerStrongLogDefect L (deningerStrongLogDefect M g) =
      deningerStrongLogDefect M (deningerStrongLogDefect L g) := by
  apply Subtype.ext
  funext t
  simp only [deningerStrongLogDefect_apply]
  rw [show t + L + M = t + M + L by ring]
  ring

/-- Every selected period has an original-source Green primitive. -/
theorem deningerStrongLogFiniteDepletion_mem_range (L : ℝ) (P : List ℝ)
    (hL : L ∈ P) (g : DeningerMeyerStrongLogTarget) :
    deningerStrongLogFiniteDepletion P g ∈ LinearMap.range (deningerStrongLogDefect L) := by
  induction P with
  | nil => simp at hL
  | cons M P ih =>
      rcases List.mem_cons.mp hL with rfl | hmem
      · exact ⟨deningerStrongLogFiniteDepletion P g, rfl⟩
      · obtain ⟨u, hu⟩ := ih hmem
        refine ⟨deningerStrongLogDefect M u, ?_⟩
        change deningerStrongLogDefect L (deningerStrongLogDefect M u) =
          deningerStrongLogDefect M (deningerStrongLogFiniteDepletion P g)
        rw [deningerStrongLogDefect_comm, hu]

/-- Every finite Xi packet is realized in all of the specified original prime Green domains. -/
theorem deningerFinitePrimeGreenDomain_jet_interpolation
    (P : List Nat.Primes) (S : Finset XiDivisorSupport)
    (v : DeningerMeyerFiniteXiJetPacket S) :
    ∃ g : DeningerMeyerStrongLogTarget,
      (∀ p ∈ P, g ∈ LinearMap.range (deningerStrongLogDefect (Real.log (p : ℕ)))) ∧
      deningerMeyerFiniteXiJetPacketLM S (Submodule.Quotient.mk g) = v := by
  let periods := P.map (fun (p : Nat.Primes) => Real.log (p : ℕ))
  have hpos : ∀ L ∈ periods, 0 < L := by
    intro L hL
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hL
    exact Real.log_pos (by exact_mod_cast p.property.one_lt)
  obtain ⟨g, hg⟩ := deningerStrongLogFiniteDepletion_jet_surjective S periods hpos v
  refine ⟨deningerStrongLogFiniteDepletion periods g, ?_, hg⟩
  intro p hp
  exact deningerStrongLogFiniteDepletion_mem_range _ periods (List.mem_map.mpr ⟨p, hp, rfl⟩) g

/-- The first nonzero Mellin derivative is multiplied by the same Euler character. -/
theorem deningerStrongLogDefect_leading_jet (L : ℝ) (g : DeningerMeyerStrongLogTarget)
    (k : ℕ) (s : ℂ) (hlower : ∀ j < k, deningerMeyerStrongLogMellinJetLM j s g = 0) :
    deningerMeyerStrongLogMellinJetLM k s (deningerStrongLogDefect L g) =
      (1 - Complex.exp (((-L : ℝ) : ℂ) * s)) * deningerMeyerStrongLogMellinJetLM k s g := by
  rw [deningerStrongLogDefect, LinearMap.sub_apply, LinearMap.id_apply, map_sub,
    deningerMeyerStrongLogMellinJetLM_flow, Finset.sum_eq_single 0]
  · simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.sub_zero]
    ring
  · intro i hi hi0
    rw [hlower (k-i) (by have := Finset.mem_range.mp hi; omega)]
    simp
  · simp

/-- The canonical strong-log landing intertwines the literal Euler defects. -/
theorem deningerExpSchwartzOfStrongLogDecay_defect (L : ℝ)
    (g : DeningerMeyerStrongLogTarget) :
    deningerExpSchwartzOfStrongLogDecay (deningerStrongLogDefect L g).val
        (deningerStrongLogDefect L g).property =
      deningerPeriodizationDefect L (deningerExpSchwartzOfStrongLogDecay g.val g.property) := by
  apply Subtype.ext
  ext t
  rw [deningerPeriodizationDefect_apply]
  exact deningerStrongLogDefect_apply L g t

/-- A common strong-log Green domain for infinitely many primes is zero. -/
theorem deningerInfinitePrimeGreenDomain_eq_zero
    {Q : Set ℕ} (hQ : Q.Infinite) (hprime : ∀ p ∈ Q, Nat.Prime p)
    (g : DeningerMeyerStrongLogTarget)
    (hg : ∀ p ∈ Q, g ∈ LinearMap.range (deningerStrongLogDefect (Real.log p))) : g = 0 := by
  let f := deningerExpSchwartzOfStrongLogDecay g.val g.property
  have hf := deningerCofinalPrimeTomography f.property hQ hprime (fun p hp => ?_)
  · apply Subtype.ext
    funext t
    exact congrArg (fun u : SchwartzMap ℝ ℂ => u t) hf
  · obtain ⟨u, hu⟩ := hg p hp
    have hmem : f ∈ Set.range (deningerPeriodizationDefect (Real.log p)) := by
      refine ⟨deningerExpSchwartzOfStrongLogDecay u.val u.property, ?_⟩
      rw [← deningerExpSchwartzOfStrongLogDecay_defect, hu]
    rw [deningerPeriodization_range_eq_kernel
      (Real.log_pos (by exact_mod_cast (hprime p hp).one_lt))] at hmem
    exact hmem

/-- A retained nonzero finite Xi packet excludes complete Gamma/flux cancellation. -/
theorem deningerFiniteXiJet_nonzero_gamma_ne_transgression
    (S : Finset XiDivisorSupport) (g : DeningerMeyerStrongLogTarget)
    (hg : deningerMeyerFiniteXiJetPacketLM S (Submodule.Quotient.mk g) ≠ 0) :
    let h := DeningerMeyerSource.toSource.symm
      (deningerExpSchwartzOfStrongLogDecay g.val g.property)
    deningerAdiabaticGammaBoundary h ≠ deningerAdiabaticGreenStokesTransgression h := by
  dsimp only
  intro heq
  obtain ⟨f, hf⟩ := (deningerAdiabaticGamma_eq_transgression_iff_poisson _).1 heq
  have hfg : deningerMeyerStrongLogSumLM f = g := by
    apply Subtype.ext
    funext t
    have ht := congrFun (deningerPoissonSource_coe_eq_strongLogSum f) t
    rw [hf] at ht
    exact ht.symm
  have hz : (Submodule.Quotient.mk g : DeningerMeyerStrongLogCohomology) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 ⟨f, hfg⟩
  exact hg (by rw [hz, map_zero])

/-- The actual Gaussian finite packet is nonzero whenever its original Xi anchor is retained. -/
theorem deningerReflectedGaussian_finiteJetPacket_ne_zero
    (S : Finset XiDivisorSupport) (rho : XiDivisorSupport) (hrho : rho ∈ S) :
    deningerMeyerFiniteXiJetPacketLM S
      (Submodule.Quotient.mk deningerMeyerReflectedLogGaussianSource) ≠ 0 := by
  intro hz
  have he := congrFun hz
    (⟨⟨rho, hrho⟩, ⟨0, xiSupportMultiplicity_pos rho⟩⟩ : DeningerMeyerFiniteXiJetSlot S)
  change deningerMeyerXiSupportJetEvaluationLM rho ⟨0, xiSupportMultiplicity_pos rho⟩
    (Submodule.Quotient.mk deningerMeyerReflectedLogGaussianSource) = 0 at he
  rw [deningerMeyerXiSupportJetEvaluationLM_mk,
    deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv, iteratedDeriv_zero] at he
  exact deningerMeyerReflectedLogGaussianSource_mellin_ne_zero rho he

/-- Every original finite prime list admits a complete source retaining the Gaussian's entire
selected Xi packet and its nonzero Gamma/flux discrepancy. -/
theorem deningerFinitePrimeGreenDomain_retained_gaussian_packet
    (P : List Nat.Primes) (S : Finset XiDivisorSupport)
    (rho : XiDivisorSupport) (hrho : rho ∈ S) :
    ∃ g : DeningerMeyerStrongLogTarget,
      (∀ p ∈ P, g ∈ LinearMap.range (deningerStrongLogDefect (Real.log (p : ℕ)))) ∧
      deningerMeyerFiniteXiJetPacketLM S (Submodule.Quotient.mk g) =
        deningerMeyerFiniteXiJetPacketLM S
          (Submodule.Quotient.mk deningerMeyerReflectedLogGaussianSource) ∧
      (let h := DeningerMeyerSource.toSource.symm
        (deningerExpSchwartzOfStrongLogDecay g.val g.property)
       deningerAdiabaticGammaBoundary h ≠ deningerAdiabaticGreenStokesTransgression h) := by
  obtain ⟨g, hdomains, hpacket⟩ := deningerFinitePrimeGreenDomain_jet_interpolation P S
    (deningerMeyerFiniteXiJetPacketLM S
      (Submodule.Quotient.mk deningerMeyerReflectedLogGaussianSource))
  refine ⟨g, hdomains, hpacket, deningerFiniteXiJet_nonzero_gamma_ne_transgression S g ?_⟩
  rw [hpacket]
  exact deningerReflectedGaussian_finiteJetPacket_ne_zero S rho hrho

/-- The uncentered Euler defect multiplies the entire Mellin transform. -/
theorem deningerStrongLogDefect_mellin (L : ℝ) (g : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerStrongLogMellin (deningerStrongLogDefect L g) s =
      (1 - Complex.exp (((-L : ℝ) : ℂ) * s)) * deningerMeyerStrongLogMellin g s := by
  simpa only [deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv, iteratedDeriv_zero] using
    deningerStrongLogDefect_leading_jet L g 0 s (by intro j hj; omega)

/-- An Euler defect together with its actual weighted-reflection mate. -/
def deningerStrongLogPairedEulerDefect (L : ℝ) :
    DeningerMeyerStrongLogTarget →ₗ[ℂ] DeningerMeyerStrongLogTarget :=
  (deningerStrongLogDefect L).comp
    (deningerMeyerStrongLogJ.comp ((deningerStrongLogDefect L).comp deningerMeyerStrongLogJ))

/-- The paired defect has a reflection-symmetric, nowhere-zero strip multiplier. -/
theorem deningerStrongLogPairedEulerDefect_mellin (L : ℝ)
    (g : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerStrongLogMellin (deningerStrongLogPairedEulerDefect L g) s =
      ((1 - Complex.exp (((-L : ℝ) : ℂ) * s)) *
        (1 - Complex.exp (((-L : ℝ) : ℂ) * (1-s)))) * deningerMeyerStrongLogMellin g s := by
  change deningerMeyerStrongLogMellin
    (deningerStrongLogDefect L (deningerMeyerStrongLogJ
      (deningerStrongLogDefect L (deningerMeyerStrongLogJ g)))) s = _
  rw [deningerStrongLogDefect_mellin, deningerMeyerStrongLogMellin_J,
    deningerStrongLogDefect_mellin, deningerMeyerStrongLogMellin_J]
  rw [show 1 - (1-s) = s by ring]
  ring

/-- Paired depletion preserves the original collar involution. -/
theorem deningerStrongLogPairedEulerDefect_J (L : ℝ) (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogJ (deningerStrongLogPairedEulerDefect L g) =
      deningerStrongLogPairedEulerDefect L (deningerMeyerStrongLogJ g) := by
  apply deningerMeyerStrongLogMellin_injective
  funext s
  dsimp only
  rw [deningerMeyerStrongLogMellin_J, deningerStrongLogPairedEulerDefect_mellin,
    deningerStrongLogPairedEulerDefect_mellin, deningerMeyerStrongLogMellin_J]
  rw [show 1 - (1-s) = s by ring]
  ring

/-- A paired factor commutes with every original Euler factor. -/
theorem deningerStrongLogPairedEulerDefect_comm (L M : ℝ) (g : DeningerMeyerStrongLogTarget) :
    deningerStrongLogPairedEulerDefect L (deningerStrongLogDefect M g) =
      deningerStrongLogDefect M (deningerStrongLogPairedEulerDefect L g) := by
  apply deningerMeyerStrongLogMellin_injective
  funext s
  dsimp only
  rw [deningerStrongLogPairedEulerDefect_mellin, deningerStrongLogDefect_mellin,
    deningerStrongLogDefect_mellin, deningerStrongLogPairedEulerDefect_mellin]
  ring

/-- Ordered paired depletion, retaining repeated original prime depths. -/
def deningerStrongLogPairedDepletion : List ℝ →
    DeningerMeyerStrongLogTarget →ₗ[ℂ] DeningerMeyerStrongLogTarget
  | [] => LinearMap.id
  | L :: P => (deningerStrongLogPairedEulerDefect L).comp (deningerStrongLogPairedDepletion P)

/-- Every original prime Green primitive remains admitted after all paired factors. -/
theorem deningerStrongLogPairedDepletion_mem_range (L : ℝ) (P : List ℝ)
    (hL : L ∈ P) (g : DeningerMeyerStrongLogTarget) :
    deningerStrongLogPairedDepletion P g ∈ LinearMap.range (deningerStrongLogDefect L) := by
  induction P with
  | nil => simp at hL
  | cons M P ih =>
      rcases List.mem_cons.mp hL with rfl | hmem
      · exact ⟨deningerMeyerStrongLogJ (deningerStrongLogDefect L
          (deningerMeyerStrongLogJ (deningerStrongLogPairedDepletion P g))), rfl⟩
      · obtain ⟨u, hu⟩ := ih hmem
        refine ⟨deningerStrongLogPairedEulerDefect M u, ?_⟩
        change deningerStrongLogDefect L (deningerStrongLogPairedEulerDefect M u) =
          deningerStrongLogPairedEulerDefect M (deningerStrongLogPairedDepletion P g)
        rw [← deningerStrongLogPairedEulerDefect_comm, hu]

/-- The full finite paired source commutes with collar exchange. -/
theorem deningerStrongLogPairedDepletion_J (P : List ℝ) (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogJ (deningerStrongLogPairedDepletion P g) =
      deningerStrongLogPairedDepletion P (deningerMeyerStrongLogJ g) := by
  induction P with
  | nil => rfl
  | cons L P ih =>
      change deningerMeyerStrongLogJ
        (deningerStrongLogPairedEulerDefect L (deningerStrongLogPairedDepletion P g)) = _
      rw [deningerStrongLogPairedEulerDefect_J, ih]
      rfl

/-- Exact normalization retained by the complete finite paired source. -/
theorem deningerStrongLogPairedDepletion_mellin (P : List ℝ)
    (g : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerStrongLogMellin (deningerStrongLogPairedDepletion P g) s =
      (P.map (fun L => (1 - Complex.exp (((-L : ℝ) : ℂ) * s)) *
        (1 - Complex.exp (((-L : ℝ) : ℂ) * (1-s))))).prod *
        deningerMeyerStrongLogMellin g s := by
  induction P with
  | nil => simp [deningerStrongLogPairedDepletion]
  | cons L P ih =>
      change deningerMeyerStrongLogMellin
        (deningerStrongLogPairedEulerDefect L (deningerStrongLogPairedDepletion P g)) s = _
      rw [deningerStrongLogPairedEulerDefect_mellin, ih]
      simp only [List.map_cons, List.prod_cons]
      ring

private theorem one_sub_eulerCharacter_ne_zero {L : ℝ} (hL : 0 < L)
    {s : ℂ} (hs : 0 < s.re) : 1 - Complex.exp (((-L : ℝ) : ℂ) * s) ≠ 0 := by
  intro h
  have hn := congrArg norm (sub_eq_zero.mp h).symm
  rw [Complex.norm_exp, norm_one] at hn
  have hz := Real.exp_injective (hn.trans Real.exp_zero.symm)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hz
  have hneg : -L * s.re < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos hL) hs
  linarith

/-- Paired finite Green admission loses no nonzero spectral value in the open strip. -/
theorem deningerStrongLogPairedDepletion_mellin_ne_zero (P : List ℝ)
    (hP : ∀ L ∈ P, 0 < L) (g : DeningerMeyerStrongLogTarget)
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1)
    (hg : deningerMeyerStrongLogMellin g s ≠ 0) :
    deningerMeyerStrongLogMellin (deningerStrongLogPairedDepletion P g) s ≠ 0 := by
  induction P with
  | nil => exact hg
  | cons L P ih =>
      change deningerMeyerStrongLogMellin
        (deningerStrongLogPairedEulerDefect L (deningerStrongLogPairedDepletion P g)) s ≠ 0
      rw [deningerStrongLogPairedEulerDefect_mellin]
      apply mul_ne_zero
      · exact mul_ne_zero
          (one_sub_eulerCharacter_ne_zero (hP L (by simp)) hs.1)
          (one_sub_eulerCharacter_ne_zero (hP L (by simp)) (by simp; linarith [hs.2]))
      · exact ih (fun a ha => hP a (by simp [ha]))

/-- Explicit collar-fixed Gaussian in every original finite prime Green domain, with
nonzero spectral value at every actual Xi coordinate. -/
theorem deningerPairedPrimeGreenGaussian_source (P : List Nat.Primes) :
    let g := deningerStrongLogPairedDepletion
      (P.map (fun (p : Nat.Primes) => Real.log (p : ℕ))) deningerMeyerReflectedLogGaussianSource
    deningerMeyerStrongLogJ g = g ∧
      (∀ p ∈ P, g ∈ LinearMap.range (deningerStrongLogDefect (Real.log (p : ℕ)))) ∧
      ∀ rho : XiDivisorSupport, deningerMeyerStrongLogMellin g rho ≠ 0 := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [deningerStrongLogPairedDepletion_J, deningerMeyerReflectedLogGaussianSource_J_fixed]
  · intro p hp
    exact deningerStrongLogPairedDepletion_mem_range (Real.log (p : ℕ))
      (P.map (fun (q : Nat.Primes) => Real.log (q : ℕ)))
      (List.mem_map.mpr ⟨p, hp, rfl⟩) deningerMeyerReflectedLogGaussianSource
  · intro rho
    apply deningerStrongLogPairedDepletion_mellin_ne_zero
    · intro L hL
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hL
      exact Real.log_pos (by exact_mod_cast p.property.one_lt)
    · exact xi_divisor_support_re_mem_open_unit rho
    · exact deningerMeyerReflectedLogGaussianSource_mellin_ne_zero rho

/-- Every leading derivative, including the first nonzero derivative at the original
multiplicity, retains the exact paired normalization. -/
theorem deningerStrongLogPairedDepletion_leading_jet (P : List ℝ)
    (g : DeningerMeyerStrongLogTarget) (k : ℕ) (s : ℂ)
    (hlower : ∀ j < k, deningerMeyerStrongLogMellinJetLM j s g = 0) :
    deningerMeyerStrongLogMellinJetLM k s (deningerStrongLogPairedDepletion P g) =
      (P.map (fun L => (1 - Complex.exp (((-L : ℝ) : ℂ) * s)) *
        (1 - Complex.exp (((-L : ℝ) : ℂ) * (1-s))))).prod *
        deningerMeyerStrongLogMellinJetLM k s g := by
  let A : ℂ → ℂ := fun z => (P.map (fun L => (1 - Complex.exp (((-L : ℝ) : ℂ) * z)) *
        (1 - Complex.exp (((-L : ℝ) : ℂ) * (1-z))))).prod
  have hA : ContDiff ℂ (k : WithTop ℕ∞) A := by
    dsimp only [A]
    induction P with
    | nil => simpa using (contDiff_const : ContDiff ℂ (k : WithTop ℕ∞) (fun _ : ℂ => (1 : ℂ)))
    | cons L P ih =>
        simp only [List.map_cons, List.prod_cons]
        exact (by fun_prop : ContDiff ℂ (k : WithTop ℕ∞)
          (fun z : ℂ => (1 - Complex.exp (((-L : ℝ) : ℂ) * z)) *
            (1 - Complex.exp (((-L : ℝ) : ℂ) * (1-z))))).mul ih
  have hg : ContDiff ℂ (k : WithTop ℕ∞) (deningerMeyerStrongLogMellin g) :=
    (differentiable_deningerMeyerStrongLogMellin g.property).contDiff.of_le le_top
  have hfun : deningerMeyerStrongLogMellin (deningerStrongLogPairedDepletion P g) =
      A * deningerMeyerStrongLogMellin g := by
    funext z
    exact deningerStrongLogPairedDepletion_mellin P g z
  rw [deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv, hfun,
    iteratedDeriv_mul hA.contDiffAt hg.contDiffAt, Finset.sum_eq_single 0]
  · simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero,
      Nat.sub_zero, deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv]
    rfl
  · intro i hi hi0
    have hz := hlower (k-i) (by have := Finset.mem_range.mp hi; omega)
    rw [deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv] at hz
    rw [hz]
    simp
  · simp

/-- The explicit collar-fixed paired Gaussian has a nonzero complete Gamma/flux boundary,
for every finite list of original primes, without selecting any zero off the critical line. -/
theorem deningerPairedPrimeGreenGaussian_gamma_ne_transgression (P : List Nat.Primes) :
    let g := deningerStrongLogPairedDepletion
      (P.map (fun (p : Nat.Primes) => Real.log (p : ℕ))) deningerMeyerReflectedLogGaussianSource
    let h := DeningerMeyerSource.toSource.symm
      (deningerExpSchwartzOfStrongLogDecay g.val g.property)
    deningerAdiabaticGammaBoundary h ≠ deningerAdiabaticGreenStokesTransgression h := by
  let g := deningerStrongLogPairedDepletion
    (P.map (fun (p : Nat.Primes) => Real.log (p : ℕ))) deningerMeyerReflectedLogGaussianSource
  let rho : XiDivisorSupport := Classical.arbitrary XiDivisorSupport
  apply deningerFiniteXiJet_nonzero_gamma_ne_transgression {rho} g
  intro hz
  have he := congrFun hz
    (⟨⟨rho, by simp⟩, ⟨0, xiSupportMultiplicity_pos rho⟩⟩ : DeningerMeyerFiniteXiJetSlot {rho})
  change deningerMeyerXiSupportJetEvaluationLM rho ⟨0, xiSupportMultiplicity_pos rho⟩
    (Submodule.Quotient.mk g) = 0 at he
  rw [deningerMeyerXiSupportJetEvaluationLM_mk,
    deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv, iteratedDeriv_zero] at he
  exact (deningerPairedPrimeGreenGaussian_source P).2.2 rho he

/-- The same explicit paired source is fixed by collar exchange in the actual
Meyer source used by the Gamma and transgression readers. -/
theorem deningerPairedPrimeGreenGaussian_exchange_fixed (P : List Nat.Primes) :
    let g := deningerStrongLogPairedDepletion
      (P.map (fun (p : Nat.Primes) => Real.log (p : ℕ))) deningerMeyerReflectedLogGaussianSource
    let h := DeningerMeyerSource.toSource.symm
      (deningerExpSchwartzOfStrongLogDecay g.val g.property)
    deningerMeyerCollarExchange h = h := by
  dsimp only
  apply DeningerMeyerSource.toSource.injective
  rw [deningerMeyerCollarExchange_toSource]
  apply Subtype.ext
  ext t
  exact congrArg (fun u : DeningerMeyerStrongLogTarget => (u : ℝ → ℂ) t)
    (deningerPairedPrimeGreenGaussian_source P).1

end
end RHTower
