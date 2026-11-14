import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt.PadicTateTower
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Reconstruction of the p-adic Tate tower

Every compatible division tower in `ℚ_p/ℤ_p` has the form
`z/pⁿ mod ℤ_p` for a unique `z ∈ ℤ_p`. Levelwise numerators yield
compatible residues modulo `pⁿ`; the inverse-limit property of `ℤ_p`
reconstructs their common numerator.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt

open GaloisForLFunctions.HTGeometry

variable (p : ℕ) [Fact p.Prime]

theorem padicDivisionPoint_eq_iff_residue_eq (n : ℕ) (z w : ℤ_[p]) :
    padicDivisionPoint p n z = padicDivisionPoint p n w ↔
      PadicInt.toZModPow n z = PadicInt.toZModPow n w := by
  calc
    padicDivisionPoint p n z = padicDivisionPoint p n w ↔
        padicDivisionPoint p n (z - w) = 0 := by rw [map_sub, sub_eq_zero]
    _ ↔ (p : ℤ_[p]) ^ n ∣ z - w := padicDivisionPoint_eq_zero_iff p n (z - w)
    _ ↔ _ := by
      rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow,
        RingHom.mem_ker, map_sub, sub_eq_zero]

/-- Compatible residues have a common p-adic lift. Polynomial evaluation converts
an element-valued inverse system to the ring-homomorphism universal property. -/
private theorem exists_padic_residues (a : ∀ n : ℕ, ZMod (p ^ n))
    (ha : ∀ i j (h : i ≤ j), ZMod.castHom (pow_dvd_pow p h) _ (a j) = a i) :
    ∃ z : ℤ_[p], ∀ n, PadicInt.toZModPow n z = a n := by
  let f (n : ℕ) : Polynomial ℤ →+* ZMod (p ^ n) :=
    Polynomial.eval₂RingHom (Int.castRingHom _) (a n)
  have hf : ∀ i j (h : i ≤ j),
      (ZMod.castHom (pow_dvd_pow p h) _).comp (f j) = f i := by
    intro i j h
    ext <;> simp [f, ha i j h]
  refine ⟨PadicInt.lift hf Polynomial.X, fun n => ?_⟩
  have h := RingHom.congr_fun (PadicInt.lift_spec hf n) Polynomial.X
  simpa [f] using h

/-- Every compatible tower has one common p-adic numerator. -/
theorem padicTateTowerEmbedding_surjective :
    Function.Surjective (padicTateTowerEmbedding p) := by
  intro x
  have hn (n : ℕ) : ∃ z : ℤ_[p], padicDivisionPoint p n z = x.1 n := by
    have hp : (p : ℤ_[p]) ^ n ≠ 0 :=
      pow_ne_zero n (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    have hx : x.1 n ∈ Submodule.torsionBy ℤ_[p] (PadicTateQuotient p) ((p : ℤ_[p]) ^ n) := by
      rw [Submodule.mem_torsionBy_iff]
      simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using x.2.2 n
    obtain ⟨z, hz⟩ := padicTateTorsionParam_surjective p ((p : ℤ_[p]) ^ n) hp ⟨x.1 n, hx⟩
    exact ⟨z, congrArg Subtype.val hz⟩
  choose z hz using hn
  have hcompat (i j : ℕ) (h : i ≤ j) :
      ZMod.castHom (pow_dvd_pow p h) _ (PadicInt.toZModPow j (z j)) =
        PadicInt.toZModPow i (z i) := by
    have hij : padicDivisionPoint p i (z j) = padicDivisionPoint p i (z i) := by
      calc
        padicDivisionPoint p i (z j) = p ^ (j - i) • padicDivisionPoint p j (z j) := by
          have ht := (tateTower_pow_smul p (padicTateTowerEmbedding p (z j)) (j - i) i).symm
          change padicDivisionPoint p i (z j) =
            p ^ (j - i) • padicDivisionPoint p (i + (j - i)) (z j) at ht
          rwa [Nat.add_sub_of_le h] at ht
        _ = p ^ (j - i) • x.1 j := by rw [hz j]
        _ = x.1 i := by
          simpa only [Nat.add_sub_of_le h] using tateTower_pow_smul p x (j - i) i
        _ = padicDivisionPoint p i (z i) := (hz i).symm
    have hc := RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow (p := p) i j h) (z j)
    exact hc.trans ((padicDivisionPoint_eq_iff_residue_eq p i _ _).mp hij)
  obtain ⟨a, ha⟩ := exists_padic_residues p (fun n => PadicInt.toZModPow n (z n)) hcompat
  refine ⟨a, Subtype.ext (funext fun n => ?_)⟩
  exact ((padicDivisionPoint_eq_iff_residue_eq p n a (z n)).mpr (ha n)).trans (hz n)

/-- The Tate module of the p-adic Tate quotient is the additive group of p-adic integers. -/
def padicTateTowerEquiv : ℤ_[p] ≃+ tateTower p (PadicTateQuotient p) :=
  AddEquiv.ofBijective (padicTateTowerEmbedding p)
    ⟨padicTateTowerEmbedding_injective p, padicTateTowerEmbedding_surjective p⟩

#print axioms padicTateTowerEmbedding_surjective
#print axioms padicTateTowerEquiv

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt
