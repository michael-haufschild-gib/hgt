import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ComplexTeichmullerPlace
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelGenerators
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TeichmullerReduction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TameKummerCharacters

/-! Lifting prime-to-characteristic roots gives a Teichmüller section. Together
with compatible finite-field generators it constructs the normalized label datum. -/

noncomputable section

open IsLocalRing ReciprocityTheory.Gal
open WindowedLandauTheory.CyclotomicNorms WindowedLandauTheory.NormalizedTypes

namespace GlobalTheory.TeichPlace

variable {p : ℕ} [Fact p.Prime]
variable {K : Type} [Field K] (A : ValuationSubring K) (κ : ResidueField A ≃+* Fbar p)

private theorem mem_of_root {z : K} {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) : z ∈ A :=
  (A.valuation_le_one_iff _).mp (valuation_eq_one_of_pow_eq_one A hn.ne' hz).le

include κ in
private theorem valuation_natCast_prime_lt_one : A.valuation (p : K) < 1 := by
  have hp : κ (residue A (p : A)) = 0 := by
    rw [map_natCast, map_natCast, CharP.cast_eq_zero (Fbar p) p]
  have hq := κ.injective (hp.trans (map_zero κ).symm)
  have h := (A.valuation_lt_one_iff (p : A)).mp ((residue_eq_zero_iff _).mp hq)
  simpa only [SubringClass.coe_natCast] using h

private theorem redThrough_mul_of_mem {x y : K} (hx : x ∈ A) (hy : y ∈ A) :
    redThrough A κ (x * y) = redThrough A κ x * redThrough A κ y := by
  simp only [redThrough, dif_pos (mul_mem hx hy), dif_pos hx, dif_pos hy]
  exact map_mul (κ.toRingHom.comp (residue A)) (⟨x, hx⟩ : A) ⟨y, hy⟩

private theorem redThrough_one_eq : redThrough A κ 1 = 1 := by
  rw [redThrough, dif_pos (one_mem A)]
  change κ (residue A 1) = 1
  rw [map_one, map_one]

theorem eq_of_reduced_root_eq {x y : K} {n : ℕ} (hn : 0 < n) (hc : p.Coprime n)
    (hx : x ^ n = 1) (hy : y ^ n = 1) (he : redThrough A κ x = redThrough A κ y) : x = y := by
  apply eq_of_pow_eq_one A (GlobalTheory.TameKummer.natCast_valuation_not_lt_one A
    (valuation_natCast_prime_lt_one A κ) hc) hx hy
  have hX := mem_of_root A hn hx
  have hY := mem_of_root A hn hy
  simp only [redThrough, dif_pos hX, dif_pos hY, κ.injective.eq_iff] at he
  have hsub : (⟨x, hX⟩ : A) - ⟨y, hY⟩ ∈ maximalIdeal A := by
    apply Ideal.Quotient.eq.mp
    exact he
  exact (A.valuation_lt_one_iff _).mp hsub

/-- A characteristic-zero algebraically closed field admits a multiplicative
Teichmüller section at any valuation with the specified algebraic residue field. -/
theorem exists_teich_of_residue [IsAlgClosed K] [CharZero K] :
    ∃ t : Fbar p →* K, IsTeich A κ t ∧ Function.Injective t := by
  classical
  have hlift (x : Fbar p) : ∃ y : K, y ∈ A ∧ redThrough A κ y = x ∧
      (x = 0 → y = 0) ∧ (x ≠ 0 → ∃ n : ℕ, 0 < n ∧ p.Coprime n ∧ y ^ n = 1) := by
    by_cases hx : x = 0
    · subst x
      refine ⟨0, zero_mem A, ?_, fun _ => rfl, fun h => (h rfl).elim⟩
      rw [redThrough, dif_pos (zero_mem A)]
      change κ (residue A 0) = 0
      rw [map_zero, map_zero]
    · obtain ⟨n, hn, hc, hp⟩ := fbar_exists_coprime_pow_eq_one hx
      obtain ⟨y, hy, hr⟩ := exists_rootOfUnity_lift A κ hn hc hp
      exact ⟨y, mem_of_root A hn hy, hr, fun h => (hx h).elim, fun _ => ⟨n, hn, hc, hy⟩⟩
  choose t ht using hlift
  have hone : t 1 = 1 := by
    obtain ⟨n, hn, hc, hp⟩ := (ht 1).2.2.2 one_ne_zero
    exact eq_of_reduced_root_eq A κ hn hc hp (one_pow n)
      ((ht 1).2.1.trans (redThrough_one_eq A κ).symm)
  have hmul (x y : Fbar p) : t (x * y) = t x * t y := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp [(ht 0).2.2.1 rfl]
    rcases eq_or_ne y 0 with rfl | hy
    · simp [(ht 0).2.2.1 rfl]
    obtain ⟨a, ha, hpa, hax⟩ := (ht x).2.2.2 hx
    obtain ⟨b, hb, hpb, hby⟩ := (ht y).2.2.2 hy
    obtain ⟨c, hc, hpc, hcz⟩ := (ht (x * y)).2.2.2 (mul_ne_zero hx hy)
    have hpow {z : K} {i j : ℕ} (hz : z ^ i = 1) (hij : i ∣ j) : z ^ j = 1 := by
      obtain ⟨k, rfl⟩ := hij
      rw [pow_mul, hz, one_pow]
    apply eq_of_reduced_root_eq A κ (Nat.mul_pos (Nat.mul_pos ha hb) hc)
      ((hpa.mul_right hpb).mul_right hpc)
      (hpow hcz (dvd_mul_left c (a * b)))
    · rw [mul_pow, hpow hax (dvd_mul_right a b |>.trans (dvd_mul_right (a * b) c)),
        hpow hby (dvd_mul_left b a |>.trans (dvd_mul_right (a * b) c)), one_mul]
    · rw [redThrough_mul_of_mem A κ (ht x).1 (ht y).1, (ht x).2.1, (ht y).2.1, (ht (x * y)).2.1]
  refine ⟨{ toFun := t, map_one' := hone, map_mul' := hmul }, ?_, ?_⟩
  · intro x
    have h := (ht x).2.1
    rw [redThrough, dif_pos (ht x).1] at h
    exact ⟨(ht x).1, h⟩
  · intro x y h
    exact ((ht x).2.1.symm.trans (congrArg (redThrough A κ) h)).trans (ht y).2.1

/-- A multiplicative lift from a prime-field algebraic closure is integral
at every valuation. -/
theorem lift_mem {g : ℕ} [Fact g.Prime] (t : Fbar g →* K) (x : Fbar g) :
    t x ∈ A := by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases eq_or_ne (t 0) 0 with h | h
    · rw [h]; exact zero_mem A
    · have he : t 0 * t 0 = t 0 := by rw [← map_mul, mul_zero]
      rw [(mul_eq_left₀ h).mp he]; exact one_mem A
  · obtain ⟨n, hn, -, hp⟩ := fbar_exists_coprime_pow_eq_one hx
    exact mem_of_root A hn (by rw [← map_pow, hp, map_one])

/-- Reduction of a multiplicative lift is defined on the entire algebraic closure
of the source prime field because its nonzero elements have finite order. -/
def reduceLift {g : ℕ} [Fact g.Prime] (t : Fbar g →* K) : Fbar g →* Fbar p where
  toFun x := redThrough A κ (t x)
  map_one' := by rw [map_one, redThrough_one_eq]
  map_mul' x y := by rw [map_mul, redThrough_mul_of_mem A κ (lift_mem A t x) (lift_mem A t y)]

/-- The reduction distinguishes any two elements whose orders are prime to
the characteristic of the target residue field. -/
theorem reduceLift_inj_of_coprime {g : ℕ} [Fact g.Prime] (t : Fbar g →* K)
    (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y)
    {x y : Fbar g} (hx : x ≠ 0) (hy : y ≠ 0)
    (hpx : (orderOf x).Coprime p) (hpy : (orderOf y).Coprime p)
    (h : reduceLift A κ t x = reduceLift A κ t y) : x = y := by
  have hpos {z : Fbar g} (hz : z ≠ 0) : 0 < orderOf z := by
    obtain ⟨n, hn, -, hp⟩ := fbar_exists_coprime_pow_eq_one hz
    exact (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hp⟩).orderOf_pos
  apply ht x y hx hy
  apply eq_of_reduced_root_eq A κ (Nat.mul_pos (hpos hx) (hpos hy))
    (hpx.symm.mul_right hpy.symm) _ _ h
  · rw [pow_mul, ← map_pow, pow_orderOf_eq_one, map_one, one_pow]
  · rw [mul_comm, pow_mul, ← map_pow, pow_orderOf_eq_one, map_one, one_pow]

end GlobalTheory.TeichPlace

namespace GlobalTheory.GLq.LabelModel

/-- A normalized label datum exists at each prime, with its multiplicative
lift realized at a place of the complex field. -/
theorem exists_labelDatum_isTeich (p : ℕ) [Fact p.Prime] :
    ∃ (L : LabelDatum p) (A : ValuationSubring ℂ) (κ : ResidueField A ≃+* Fbar p),
      IsTeich A κ L.teich := by
  obtain ⟨A, ⟨κ⟩⟩ := TeichPlace.exists_complex_place_residueField p
  obtain ⟨t, ht, hti⟩ := TeichPlace.exists_teich_of_residue A κ
  obtain ⟨L, hL⟩ := inhab_teich p t (fun _ _ _ _ h => hti h)
  exact ⟨L, A, κ, by rw [hL]; exact ht⟩

end GlobalTheory.GLq.LabelModel
