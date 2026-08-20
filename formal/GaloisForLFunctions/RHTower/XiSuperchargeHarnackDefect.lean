/-
# The persistent Harnack defect of a Xi zero packet

For a finite packet of zeros of the centred completed function, closed under conjugation, the
Harnack defect of the supercharge curve `y² = t · R(t)` is exactly half the number of nonreal
members of the packet.  It therefore vanishes for every packet exactly when the Riemann hypothesis
holds.

The real-topology input — that a branch polynomial with `2r + 1` simple real roots is positive on
exactly `r + 1` of the `2r + 2` complementary arcs of the real projective line, one real oval each
— is `HTGeometry.card_positive_arcs`.
-/
import GaloisForLFunctions.HTGeometry.RealBranchArcCount
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence
import GaloisForLFunctions.RHTower.XiEntireReal

noncomputable section

open Complex Finset
open scoped ComplexConjugate

namespace RHTower

/-- **The defect is a divisor recorder.**  For a packet of `2n` distinct points of which `2r` are
real, twice the Harnack defect is the number of nonreal members. -/
theorem two_mul_defect_eq_card_nonreal {Z : Finset ℂ} {n r : ℕ}
    (hZ : Z.card = 2 * n) (hR : (Z.filter (fun z => z.im = 0)).card = 2 * r) :
    2 * (n - r) = (Z.filter (fun z => z.im ≠ 0)).card := by
  classical
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Z) (p := fun z : ℂ => z.im = 0)
  rw [hR, hZ] at hsplit
  have hle : 2 * r ≤ 2 * n := by omega
  have hrn : r ≤ n := by omega
  have hfilter : (Z.filter (fun z => ¬ (z.im = 0))) = Z.filter (fun z => z.im ≠ 0) := rfl
  rw [hfilter] at hsplit
  omega

/-- **Vanishing defect is reality of the packet.** -/
theorem defect_eq_zero_iff {Z : Finset ℂ} {n r : ℕ}
    (hZ : Z.card = 2 * n) (hR : (Z.filter (fun z => z.im = 0)).card = 2 * r) :
    n - r = 0 ↔ ∀ z ∈ Z, z.im = 0 := by
  classical
  have htwo := two_mul_defect_eq_card_nonreal hZ hR
  constructor
  · intro hdef z hz
    by_contra hcon
    have hmem : z ∈ Z.filter (fun z => z.im ≠ 0) := Finset.mem_filter.mpr ⟨hz, hcon⟩
    have hpos : 0 < (Z.filter (fun z => z.im ≠ 0)).card := Finset.card_pos.mpr ⟨z, hmem⟩
    omega
  · intro hall
    have hempty : (Z.filter (fun z => z.im ≠ 0)) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr (fun z hz => ?_)
      simpa using hall z hz
    rw [hempty, Finset.card_empty] at htwo
    omega

/-- The Riemann hypothesis in the centred supercharge coordinate. -/
theorem riemannHypothesis_iff_XiC_zeros_real :
    RiemannHypothesis ↔ ∀ t : ℂ, XiC t = 0 → t.im = 0 := by
  rw [riemannHypothesis_iff_xi_zero_re_eq_half]
  constructor
  · intro h t ht
    have hxi : xi (1 / 2 + t * Complex.I) = 0 := ht
    have hre := h _ hxi
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.div_re,
      Complex.one_re, Complex.one_im] at hre
    norm_num at hre
    linarith
  · intro h ρ hρ
    have hval : XiC ((ρ - 1 / 2) * (-Complex.I)) = 0 := by
      rw [XiC]
      have harg : (1 : ℂ) / 2 + ((ρ - 1 / 2) * (-Complex.I)) * Complex.I = ρ := by
        have hI : (-Complex.I) * Complex.I = (1 : ℂ) := by
          rw [neg_mul, Complex.I_mul_I]
          ring
        rw [mul_assoc, hI, mul_one]
        ring
      rw [harg]
      exact hρ
    have him := h _ hval
    simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.div_re, Complex.div_im, Complex.one_re,
      Complex.one_im] at him
    norm_num at him
    linarith

/-- **The persistent defect criterion.**  The Riemann hypothesis is equivalent to the vanishing of
the Harnack defect of every finite conjugation-closed packet of zeros of the centred completed
function. -/
theorem riemannHypothesis_iff_forall_packet_defect_zero :
    RiemannHypothesis ↔ ∀ (Z : Finset ℂ) (n r : ℕ), (∀ z ∈ Z, XiC z = 0) →
      Z.card = 2 * n → (Z.filter (fun z => z.im = 0)).card = 2 * r → n - r = 0 := by
  classical
  constructor
  · intro hRH Z n r hzero hZ hR
    refine (defect_eq_zero_iff hZ hR).mpr (fun z hz => ?_)
    exact (riemannHypothesis_iff_XiC_zeros_real.mp hRH) z (hzero z hz)
  · intro hall
    refine riemannHypothesis_iff_XiC_zeros_real.mpr (fun t ht => ?_)
    by_contra hcon
    have hconj : XiC (conj t) = 0 := by
      rw [XiC_conj, ht]
      simp
    have hne : conj t ≠ t := by
      intro h
      have := congrArg Complex.im h
      simp only [Complex.conj_im] at this
      exact hcon (by linarith)
    set Z : Finset ℂ := {t, conj t} with hZdef
    have hcard : Z.card = 2 * 1 := by
      rw [hZdef, Finset.card_insert_of_notMem (by simpa using fun h => hne h.symm),
        Finset.card_singleton]
    have hcardR : (Z.filter (fun z => z.im = 0)).card = 2 * 0 := by
      have himT : t.im ≠ 0 := hcon
      have himC : (conj t).im ≠ 0 := by
        simp only [Complex.conj_im]
        intro h
        exact hcon (by linarith)
      have hempty : Z.filter (fun z => z.im = 0) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr (fun z hz => ?_)
        rw [hZdef] at hz
        rcases Finset.mem_insert.mp hz with h | h
        · rw [h]; exact himT
        · rw [Finset.mem_singleton.mp h]; exact himC
      rw [hempty, Finset.card_empty]
    have hzero : ∀ z ∈ Z, XiC z = 0 := by
      intro z hz
      rw [hZdef] at hz
      rcases Finset.mem_insert.mp hz with h | h
      · rw [h]; exact ht
      · rw [Finset.mem_singleton.mp h]; exact hconj
    have := hall Z 1 0 hzero hcard hcardR
    omega

end RHTower
