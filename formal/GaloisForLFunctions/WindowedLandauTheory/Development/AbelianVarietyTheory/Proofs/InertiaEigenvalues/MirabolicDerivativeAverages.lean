import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedTailMeans
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicExpansion
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerClassFunctions

/-! A zero-frequency column mean after the twisted tail averages is
Harish–Chandra restriction followed by the right Whittaker trace. -/

noncomputable section
open Matrix GaloisForLFunctions
open scoped Classical

namespace GlobalTheory.GLq

variable {g a b : ℕ} [Fact g.Prime]

local notation "Rect" => fun i j : ℕ => Matrix (Fin i) (Fin j) (ZMod g)
local notation "U" => upperUnitriangular g

omit [Fact g.Prime] in
private theorem rect_card :
    (Nat.card (Rect a b) : ℂ) = (g : ℂ) ^ (a * b) := by
  have h : Nat.card (Rect a b) = g ^ (a * b) := by
    change Nat.card (Fin a → Fin b → ZMod g) = _
    rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin, Nat.card_zmod,
      ← pow_mul, Nat.mul_comm b a]
  exact_mod_cast h

/-- Twisting only the right unipotent block gives the Whittaker derivative. -/
theorem der_eq_tailAverage_zero (ψ : AddChar (ZMod g) ℂ) (F : Gn g (a + b) → ℂ) :
    der ψ a F = tailAverage (a := a) (b := b) ψ (fun _ => 0) F := by
  funext A
  change wh ψ (res a (a + b - a) F A) = _
  rw [Nat.add_sub_cancel_left]
  rw [wh_eq_restricted_pairing_of_function, characterPairing]
  simp_rw [res_eq_sum_rectangle]
  unfold tailAverage
  rw [Nat.card_prod, Nat.cast_mul, rect_card, mul_inv, Fintype.sum_prod_type]
  simp only [AddChar.map_zero_eq_one, one_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (U b))) (t := (Finset.univ : Finset (Rect a b)))]
  refine Finset.sum_congr rfl fun X _ => Finset.sum_congr rfl fun D _ => ?_
  rw [map_inv (whittakerCharacter ψ b), Units.val_inv_eq_inv_val]
  ring

private theorem der_reindex {n m : ℕ} (h : n = m) (ψ : AddChar (ZMod g) ℂ)
    (F : Gn g n → ℂ) (i : ℕ) :
    der ψ i (fun x : Gn g m => F (reindexUnit (finCongr h.symm) x)) = der ψ i F := by
  subst m
  have hId (x : Gn g n) : reindexUnit (finCongr rfl) x = x := by
    apply Units.ext
    ext i j
    simp only [reindexUnit_apply, finCongr_refl, Equiv.refl_symm, Equiv.refl_apply]
  simp only [hId]

private theorem mirabolicFourier_zero_tailAverage (ψ : AddChar (ZMod g) ℂ)
    (F : Gn g (a + 1 + b) → ℂ) :
    (fun A : Gn g a =>
      mirabolicFourier ψ (tailAverage (a := a + 1) (b := b) ψ lastRowFirstColumn F) A 0) = der ψ a F := by
  funext A
  rw [mirabolicFourier_tailAverage]
  simp only [zero_dotProduct]
  rw [← der_eq_tailAverage_zero, der_reindex (Nat.add_assoc a 1 b)]

private theorem mirabolicTail_tailAverage {m : ℕ} (ψ : AddChar (ZMod g) ℂ)
    (F : Gn g (m + 2 + b) → ℂ) :
    mirabolicTail ψ (tailAverage (a := m + 2) (b := b) ψ lastRowFirstColumn F) =
      tailAverage (a := m + 1) (b := 1 + b) ψ lastRowFirstColumn
        (fun x => F (reindexUnit (finCongr (Nat.add_assoc (m + 1) 1 b).symm) x)) := by
  funext A
  change mirabolicFourier ψ (tailAverage (a := m + 2) (b := b) ψ lastRowFirstColumn F) A
    (Pi.single (Fin.last m) 1) = _
  rw [mirabolicFourier_tailAverage]
  have he (Y : Rect (m + 1) (1 + b)) :
      Pi.single (Fin.last m) 1 ⬝ᵥ (fun i => Y i (Fin.castAdd b 0)) = lastRowFirstColumn Y := by
    rw [single_dotProduct, one_mul, lastRowFirstColumn, dif_pos (by omega : 0 < 1 + b)]
    rfl
  rw [funext he]

/-- The recursively obtained mirabolic derivative is the usual finite
general linear group derivative after the twisted tail has been averaged. -/
theorem mirabolicDerivative_tailAverage (ψ : AddChar (ZMod g) ℂ)
    (m b : ℕ) (F : Gn g (m + 1 + b) → ℂ) (i : Fin (m + 1)) :
    mirabolicDerivative ψ m i
      (tailAverage (a := m + 1) (b := b) ψ lastRowFirstColumn F) =
        der ψ i.val F := by
  induction m generalizing b with
  | zero =>
    have hi : i = Fin.last 0 := by
      apply Fin.ext
      have h := i.isLt
      change i.val = 0
      omega
    subst i
    rw [mirabolicDerivative, Fin.lastCases_last]
    exact mirabolicFourier_zero_tailAverage ψ F
  | succ m ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [mirabolicDerivative, Fin.lastCases_last]
      exact mirabolicFourier_zero_tailAverage ψ F
    · rw [mirabolicDerivative, Fin.lastCases_castSucc, mirabolicTail_tailAverage]
      rw [ih (1 + b), der_reindex (Nat.add_assoc (m + 1) 1 b)]
      rfl

end GlobalTheory.GLq
