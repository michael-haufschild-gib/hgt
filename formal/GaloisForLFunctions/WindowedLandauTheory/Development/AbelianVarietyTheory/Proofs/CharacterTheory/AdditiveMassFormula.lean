import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.PolynomialMassRecurrence
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.PolynomialMangoldt

/-! The characteristic-polynomial mass of the Möbius inverse of an additive weight. -/

open Polynomial GlobalTheory.CuspGL

noncomputable section

namespace GlobalTheory.CuspGL.LogDeriv

variable {F : Type} [Field F]

theorem conv_congr_monic {a a' b b' : F[X] → ℂ} (ha : ∀ P : F[X], P.Monic → a P = a' P)
    (hb : ∀ P : F[X], P.Monic → b P = b' P) (P : F[X]) : conv a b P = conv a' b' P := by
  unfold conv
  refine finsum_mem_congr rfl fun x hx => ?_
  rw [ha _ hx.1, hb _ hx.2.1]

theorem pow_mul_conv (q : ℂ) (a b : F[X] → ℂ) {P : F[X]} (hP : P.Monic) :
    q ^ P.natDegree * conv a b P =
      conv (fun D => q ^ D.natDegree * a D) (fun D => q ^ D.natDegree * b D) P := by
  rw [conv_eq_sum _ _ P, conv_eq_sum _ _ P, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨h1, h2, h3⟩ := hx
  rw [← h3, h1.natDegree_mul h2, pow_add]
  ring

theorem additive_mul_conv {s : F[X] → ℂ} (hs : IsAdditive s) (a b : F[X] → ℂ) {P : F[X]}
    (hP : P.Monic) :
    s P * conv a b P = conv (fun D => s D * a D) b P + conv a (fun D => s D * b D) P := by
  rw [conv_eq_sum _ _ P, conv_eq_sum _ _ P, conv_eq_sum _ _ P, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨h1, h2, h3⟩ := hx
  rw [← h3, hs _ _ h1 h2]
  ring

theorem pow_natDegree_ne_one {q : ℕ} (hq : 2 ≤ q) {n : ℕ} (hn : n ≠ 0) : (q : ℂ) ^ n - 1 ≠ 0 := by
  rw [sub_ne_zero]
  have : q ^ n ≠ 1 := (Nat.one_lt_pow hn (by omega)).ne'
  exact_mod_cast this

theorem eq_zero_of_rec {q : ℕ} (hq : 2 ≤ q) {E : F[X] → ℂ} (h1 : E 1 = 0)
    (hE : ∀ P : F[X], P.Monic → (q : ℂ) ^ P.natDegree * E P = conv (fun _ => 1) E P) :
    ∀ P : F[X], P.Monic → E P = 0 := by
  intro P
  induction h : P.natDegree using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    intro hP
    by_cases hn : n = 0
    · rw [hP.natDegree_eq_zero.mp (h.trans hn)]; exact h1
    have key : conv (fun _ => 1) E P = E P := by
      rw [conv_eq_sum _ _ P, Finset.sum_eq_single ((1 : F[X]), P)]
      · simp
      · intro x hx hne
        rw [Set.Finite.mem_toFinset] at hx
        obtain ⟨h1, h2, h3⟩ := hx
        have hd : x.1.natDegree ≠ 0 := by
          intro h0
          have := h1.natDegree_eq_zero.mp h0
          apply hne
          rw [this, one_mul] at h3
          exact Prod.ext this h3
        have hdeg := h1.natDegree_mul h2
        rw [h3, h] at hdeg
        rw [ih x.2.natDegree (by omega) x.2 rfl h2, mul_zero]
      · intro hx
        exact absurd (by simp [hP]) hx
    have h2 := hE P hP
    rw [key, h] at h2
    have h3 : ((q : ℂ) ^ n - 1) * E P = 0 := by linear_combination h2
    exact (mul_eq_zero.mp h3).resolve_left (pow_natDegree_ne_one hq hn)

theorem mangoldt_one (s : F[X] → ℂ) : mangoldt s 1 = 0 := by
  unfold mangoldt
  refine finsum_mem_eq_zero_of_forall_eq_zero ?_
  rintro f ⟨_, hf, m, hm, h⟩
  exact absurd (IsUnit.of_pow_eq_one h.symm hm.ne') hf.not_isUnit

theorem conv_at_one (a b : F[X] → ℂ) : conv a b 1 = a 1 * b 1 := by
  unfold conv
  have : {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = 1} = {(1, 1)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hdeg := h1.natDegree_mul h2
      rw [h3, natDegree_one] at hdeg
      exact Prod.ext (h1.natDegree_eq_zero.mp (by omega)) (h2.natDegree_eq_zero.mp (by omega))
    · rintro rfl
      simp
  rw [this, finsum_mem_singleton]

theorem additive_mul_eq_conv (F : Type) [Field F] (q : ℕ) (hq : 2 ≤ q) (s m : F[X] → ℂ)
    (hs : IsAdditive s) (_hm1 : m 1 = 1)
    (hm : ∀ P : F[X], P.Monic → (q : ℂ) ^ P.natDegree * m P = conv (fun _ => 1) m P)
    (P : F[X]) (hP : P.Monic) :
    s P * m P = conv (fun D => mangoldt s D / ((q : ℂ) ^ D.natDegree - 1)) m P := by
  set L : F[X] → ℂ := fun D => mangoldt s D / ((q : ℂ) ^ D.natDegree - 1) with hL
  set o : F[X] → ℂ := fun _ => 1 with ho
  have hs1 : s 1 = 0 := by
    have := hs 1 1 monic_one monic_one
    rw [mul_one] at this
    linear_combination -this
  have hσL : ∀ D : F[X], D.Monic → (q : ℂ) ^ D.natDegree * L D = (L + mangoldt s) D := by
    intro D hD
    by_cases h0 : D.natDegree = 0
    · rw [hD.natDegree_eq_zero.mp h0]
      simp [hL, mangoldt_one]
    · have := pow_natDegree_ne_one hq h0
      simp only [hL, Pi.add_apply]
      field_simp
      ring
  have hA : ∀ Q : F[X], Q.Monic → (q : ℂ) ^ Q.natDegree * (s Q * m Q) =
      conv (conv (mangoldt s) o) m Q + conv o (fun D => s D * m D) Q := by
    intro Q hQ
    rw [mul_left_comm, hm Q hQ, additive_mul_conv hs _ _ hQ]
    congr 1
    refine conv_congr_monic (fun D hD => ?_) (fun _ _ => rfl) Q
    rw [← hs.eq_mangoldt_conv_one D hD]
    simp [ho]
  have hB : ∀ Q : F[X], Q.Monic → (q : ℂ) ^ Q.natDegree * conv L m Q =
      conv (conv (mangoldt s) o) m Q + conv o (conv L m) Q := by
    intro Q hQ
    have H := (conv_basic F Q hQ).2
    rw [pow_mul_conv _ _ _ hQ, conv_congr_monic hσL hm Q, (H L (mangoldt s) (conv o m)).2.2.1,
      (H (mangoldt s) o m).2.1, add_comm, ← (H L o m).2.1, ← (H o L m).2.1]
    congr 1
    exact conv_congr_monic (fun D hD => ((conv_basic F D hD).2 L o o).1) (fun _ _ => rfl) Q
  have hE := eq_zero_of_rec hq (E := (fun D => s D * m D) - conv L m)
    (by simp [hs1, conv_at_one, hL, mangoldt_one]) (fun Q hQ => by
      have H := (conv_basic F Q hQ).2
      rw [(H _ _ o).1, (H _ _ _).2.2.2, ← (H o _ o).1, ← (H o _ o).1, Pi.sub_apply, mul_sub,
        hA Q hQ, hB Q hQ]
      ring) P hP
  exact sub_eq_zero.mp hE

end GlobalTheory.CuspGL.LogDeriv

namespace GlobalTheory.CuspGL

/-- The Möbius-inverted weight has mass supported on powers of irreducible polynomials. -/
theorem mass_psi_eq_glCard_mul_mangoldt_div :
    ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (s : F[X] → ℂ), IsAdditive s → ∀ P : F[X], P.Monic → P.natDegree = Module.finrank F V →
      mass (psi s V) P = glCard F P.natDegree * mangoldt s P / ((Nat.card F : ℂ) ^ P.natDegree - 1) := by
  intro F _ _ V _ _ _ s hs P hP hdeg
  have hiso := psi_conj s
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hmu1 : mu (1 : F[X]) = 1 := mu_one F
  have hlog := LogDeriv.additive_mul_eq_conv F (Nat.card F) hq s mu hs hmu1 (fun Q hQ => (mu_rec F Q hQ).1)
  have hmul : ∀ Q : F[X], Q.Monic → s Q * mu Q =
      conv (fun D => mass (psi s (Fin D.natDegree → F)) D / glCard F D.natDegree) mu Q := by
    intro Q hQ
    have h := MassMult.mass_mult F (Fin Q.natDegree → F) (fun V _ _ _ => psi s V) hiso Q hQ (by simp)
    have h2 : (fun g : Module.End F (Fin Q.natDegree → F) =>
        ∑ᶠ W : {W : Submodule F (Fin Q.natDegree → F) // ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2)) =
        fun g => s (LinearMap.charpoly g) := by
      funext g
      exact (charpoly_eq_finsum_psi _ s g).symm
    rw [← h]
    rw [h2, mass_comp_charpoly_eq_mul, mu, mul_div_assoc]
  have hc := conv_cancel F _ _ mu hmu1 (fun Q hQ => (hmul Q hQ).symm.trans (hlog Q hQ)) P hP
  have hV := mass_eq_mass_pi_of_invariant (V := V) (fun V _ _ _ => psi s V) hiso P hdeg
  have hg := glCard_ne_zero_of_finite F P.natDegree
  rw [hV, mul_div_assoc, ← hc, mul_div_cancel₀ _ hg]

end GlobalTheory.CuspGL
