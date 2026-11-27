import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerFirstBlock
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitriangularBruhatExistence
import Mathlib.FieldTheory.Finite.Basic

/-! Counting the compatible monomial representatives gives the
Gelfand–Graev squared norm over the prime field. -/

noncomputable section
open scoped Classical

open GaloisForLFunctions WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace GlobalTheory.GLq.GGNorm

variable {g n : ℕ} [Fact g.Prime]

local instance : Fintype (WhittakerMonomialData g n) :=
  Fintype.ofInjective (fun D => (D.perm, D.scale))
    (fun _ _ h => WhittakerMonomialData.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

private theorem card_monomial_zero : Fintype.card (WhittakerMonomialData g 0) = 1 := by
  let d : WhittakerMonomialData g 0 :=
    ⟨Equiv.refl _, fun i => Fin.elim0 i, fun {i} => Fin.elim0 i⟩
  letI : Unique (WhittakerMonomialData g 0) :=
    ⟨⟨d⟩, fun _ => WhittakerMonomialData.ext (Equiv.ext fun i => Fin.elim0 i) (funext fun i => Fin.elim0 i)⟩
  exact Fintype.card_unique

private theorem card_monomial_succ (n : ℕ) :
    Fintype.card (WhittakerMonomialData g (n + 1)) =
      (g - 1) * ∑ a : Fin (n + 1), Fintype.card (WhittakerMonomialData g a.val) := by
  let head (D : WhittakerMonomialData g (n + 1)) := D.perm 0
  calc
    _ = Fintype.card (Σ a : Fin (n + 1), {D : WhittakerMonomialData g (n + 1) // head D = a}) :=
      Fintype.card_congr (Equiv.sigmaFiberEquiv head).symm
    _ = ∑ a : Fin (n + 1), (g - 1) * Fintype.card (WhittakerMonomialData g a.val) := by
      rw [Fintype.card_sigma]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Fintype.card_congr (WhittakerMonomialData.firstBlockEquiv (g := g) a),
        Fintype.card_prod, ZMod.card_units]
    _ = _ := (Finset.mul_sum _ _ _).symm

private theorem sum_monomial_card (n : ℕ) :
    (∑ a : Fin (n + 1), Fintype.card (WhittakerMonomialData g a.val)) = g ^ n := by
  induction n with
  | zero =>
    rw [Fin.sum_univ_one]
    exact card_monomial_zero.trans (pow_zero g).symm
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    change (∑ a : Fin (n + 1), Fintype.card (WhittakerMonomialData g a.val)) +
      Fintype.card (WhittakerMonomialData g (n + 1)) = _
    rw [card_monomial_succ, ih]
    calc
      _ = (1 + (g - 1)) * g ^ n := by rw [add_mul, one_mul]
      _ = _ := by rw [Nat.add_sub_of_le (Fact.out : g.Prime).one_le, pow_succ, mul_comm]

private def monomialCosetEquiv (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (n : ℕ) :
    WhittakerMonomialData g n ≃
      {q : DoubleCoset.Quotient (upperUnitriangular g n : Set (Gn g n)) (upperUnitriangular g n) //
        (whittakerCharacter ψ n).Intertwines (upperUnitriangular g n) q.out} := by
  let U := upperUnitriangular g n
  let χ := whittakerCharacter ψ n
  let mk := DoubleCoset.mk U U
  let F (D : WhittakerMonomialData g n) :
      {q : DoubleCoset.Quotient (U : Set (Gn g n)) U // χ.Intertwines U q.out} :=
    ⟨mk (monomialUnit D.perm D.scale),
      (χ.intertwines_doubleCoset U (DoubleCoset.out_eq' U U (mk (monomialUnit D.perm D.scale))).symm).mp
        ((intertwines_monomial_iff hψ D.perm D.scale).mpr D.compatible)⟩
  refine Equiv.ofBijective F ⟨?_, ?_⟩
  · intro D E h
    obtain ⟨h₁, h₂⟩ := monomial_data_of_doubleCoset_eq D.perm E.perm D.scale E.scale
      (congrArg Subtype.val h)
    exact WhittakerMonomialData.ext h₁ h₂
  · intro q
    obtain ⟨l, r, σ, c, h⟩ := exists_unitriangular_monomial g n q.val.out
    have e : mk (monomialUnit σ c) = mk q.val.out :=
      (DoubleCoset.eq U U _ _).mpr ⟨l, l.2, r, r.2, h⟩
    have hc : WhittakerMonomialCompatible σ c :=
      (intertwines_monomial_iff hψ σ c).mp ((χ.intertwines_doubleCoset U e).mpr q.2)
    exact ⟨⟨σ, c, hc⟩, Subtype.ext (e.trans (DoubleCoset.out_eq' U U q.val))⟩

/-- The Gelfand–Graev squared norm of a nontrivial Whittaker character in
positive rank is `g^n - g^(n-1)`. -/
theorem wh_gg (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (n : ℕ) (hn : 0 < n) :
    wh ψ (gg ψ n) = (g : ℂ) ^ n - (g : ℂ) ^ (n - 1) := by
  let U := upperUnitriangular g n
  letI := doubleCosetFintype U
  let Q := DoubleCoset.Quotient (U : Set (Gn g n)) U
  let p (q : Q) := (whittakerCharacter ψ n).Intertwines U q.out
  have he : wh ψ (gg ψ n) = (Fintype.card (WhittakerMonomialData g n) : ℂ) := by
    rw [wh_gg_eq_doubleCoset_sum]
    change (∑ q : Q, if p q then (1 : ℂ) else 0) = _
    rw [Fintype.card_congr (monomialCosetEquiv ψ hψ n), Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl fun q _ => by simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, p, U]
  rw [he]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [card_monomial_succ, sum_monomial_card, Nat.cast_mul, Nat.cast_sub (Fact.out : g.Prime).one_le,
    Nat.cast_one, Nat.cast_pow, Nat.succ_sub_one, pow_succ]
  ring

/-- A finite family of distinct generic irreducible characters is bounded
by the Gelfand–Graev norm. -/
theorem card_generic_le (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (n : ℕ) (hn : 0 < n)
    (S : Finset (Gn g n → ℂ)) (hS : ∀ χ ∈ S, IsIrr χ ∧ wh ψ χ ≠ 0) :
    S.card ≤ g ^ n - g ^ (n - 1) := by
  have h := card_le_wh_gg ψ n S hS
  have hpow : g ^ (n - 1) ≤ g ^ n :=
    Nat.pow_le_pow_right (Fact.out : g.Prime).pos (Nat.sub_le _ _)
  have e : ((g ^ n - g ^ (n - 1) : ℕ) : ℂ) = (g : ℂ) ^ n - (g : ℂ) ^ (n - 1) := by
    rw [Nat.cast_sub hpow, Nat.cast_pow, Nat.cast_pow]
  rw [wh_gg ψ hψ n hn, ← e, Complex.natCast_re] at h
  exact_mod_cast h

end GlobalTheory.GLq.GGNorm
