import GaloisForLFunctions.ArithmeticPositiveDuality.ApproximateFunctionalEquationDeterminesThePrimes
import Mathlib.Order.SuccPred.LinearLocallyFinite

/-!
# The ordered integral spectrum of a Beurling system

Summability makes every bounded norm interval finite. A prime label supplies arbitrarily larger
norms, so the distinct norms have order type ℕ. Regrouping by norm gives positive integer masses.
-/

open Set
noncomputable section
namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- A nonempty prime system with summable inverse powers has a naturally ordered norm spectrum. -/
theorem exists_ordered_beurling_norms
    (B : RHTower.BeurlingSystem) [Countable B.Label] [Nonempty B.Label]
    (hBsum : Summable fun x : B.Integer => B.intNorm x ^ (-(3 / 2 : ℝ))) :
    ∃ (lam : ℕ → ℝ) (index : B.Integer → ℕ),
      StrictMono lam ∧ lam 0 = 1 ∧ Function.Surjective index ∧
      (∀ x, lam (index x) = B.intNorm x) ∧
      (∀ n, {x : B.Integer | index x = n}.Finite) := by
  classical
  let S := Set.range B.intNorm
  letI : OrderBot S :=
    { bot := ⟨1, ⟨0, B.intNorm_zero⟩⟩
      bot_le := by
        intro x
        obtain ⟨a, ha⟩ := x.2
        change 1 ≤ x.val
        rw [← ha]
        exact B.one_le_intNorm a }
  letI : LocallyFiniteOrder S := LocallyFiniteOrder.ofFiniteIcc fun a b => by
    have hi := (finite_intNorm_le B hBsum b.val).image B.intNorm
    have hpre : (Subtype.val ⁻¹' (B.intNorm '' {x : B.Integer | B.intNorm x ≤ b.val}) : Set S).Finite :=
      hi.preimage Subtype.val_injective.injOn
    apply hpre.subset
    intro z hz
    obtain ⟨x, hx⟩ := z.2
    exact ⟨x, by change B.intNorm x ≤ b.val; rw [hx]; exact hz.2, hx⟩
  letI : SuccOrder S := LinearLocallyFiniteOrder.succOrder S
  letI : PredOrder S := LinearLocallyFiniteOrder.predOrder S
  letI : NoMaxOrder S := ⟨by
    intro a
    obtain ⟨x, hx⟩ := a.2
    let p : B.Label := Classical.choice inferInstance
    refine ⟨⟨B.intNorm (x + {p}), ⟨x + {p}, rfl⟩⟩, ?_⟩
    change a.val < B.intNorm (x + {p})
    rw [← hx, B.intNorm_add, B.intNorm_singleton]
    exact lt_mul_of_one_lt_right (B.intNorm_pos x) (B.one_lt_labelNorm p)⟩
  let e : S ≃o ℕ := orderIsoNatOfLinearSuccPredArch
  let lam : ℕ → ℝ := fun n => (e.symm n).val
  let index : B.Integer → ℕ := fun x => e ⟨B.intNorm x, ⟨x, rfl⟩⟩
  have hnorm : ∀ x, lam (index x) = B.intNorm x := by
    intro x
    exact congrArg Subtype.val (e.symm_apply_apply ⟨B.intNorm x, ⟨x, rfl⟩⟩)
  refine ⟨lam, index, ?_, ?_, ?_, hnorm, ?_⟩
  · exact fun i j hij => e.symm.strictMono hij
  · change (e.symm (⊥ : ℕ)).val = 1
    rw [e.symm.map_bot]
    rfl
  · intro n
    obtain ⟨x, hx⟩ := (e.symm n).2
    refine ⟨x, ?_⟩
    change e ⟨B.intNorm x, ⟨x, rfl⟩⟩ = n
    have he : (⟨B.intNorm x, ⟨x, rfl⟩⟩ : S) = e.symm n := Subtype.ext hx
    rw [he, e.apply_symm_apply]
  · intro n
    refine (finite_intNorm_le B hBsum (lam n)).subset fun x hx => ?_
    change B.intNorm x ≤ lam n
    rw [← hnorm x, hx]

/-- Regrouping a summable family by finite norm fibers exposes its integral multiplicities. -/
theorem sum_by_ordered_norm_fibers
    {ι V : Type*} [NormedAddCommGroup V] [CompleteSpace V]
    {index : ι → ℕ} {lam : ℕ → ℝ} {norm : ι → ℝ}
    (hnorm : ∀ x, lam (index x) = norm x)
    (hfinite : ∀ n, {x : ι | index x = n}.Finite)
    (f : ℝ → V) (hsum : Summable fun x => f (norm x)) :
    Summable (fun n => Nat.card {x : ι // index x = n} • f (lam n)) ∧
      (∑' x, f (norm x)) = ∑' n, Nat.card {x : ι // index x = n} • f (lam n) := by
  classical
  have hsig : Summable fun p : Σ n, {x : ι // index x = n} => f (norm p.2.val) :=
    ((Equiv.sigmaFiberEquiv index).summable_iff (f := fun x => f (norm x))).2 hsum
  have hfiber : ∀ n, (∑' x : {x : ι // index x = n}, f (norm x.val)) =
      Nat.card {x : ι // index x = n} • f (lam n) := by
    intro n
    letI : Fintype {x : ι // index x = n} := (hfinite n).fintype
    have he : ∀ x : {x : ι // index x = n}, norm x.val = lam n :=
      fun x => by rw [← hnorm x.val, x.property]
    simp only [he, tsum_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
  refine ⟨hsig.sigma.congr hfiber, ?_⟩
  calc (∑' x, f (norm x)) = ∑' p : Σ n, {x : ι // index x = n}, f (norm p.2.val) :=
        ((Equiv.sigmaFiberEquiv index).tsum_eq (fun x => f (norm x))).symm
    _ = ∑' n, ∑' x : {x : ι // index x = n}, f (norm x.val) := hsig.tsum_sigma
    _ = _ := tsum_congr hfiber

end GaloisForLFunctions.ArithmeticPositiveDuality
