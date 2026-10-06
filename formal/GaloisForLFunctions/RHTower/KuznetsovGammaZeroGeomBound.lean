import GaloisForLFunctions.RHTower.KuznetsovGammaZeroModulusSum

/-!
# The Kloosterman part of the `Γ₀(Q)` geometric side

For `b = gamma0Coeff a` the Kloosterman part of the `Γ₀(Q)` geometric row (`geomRow_gamma0`) is

`Σ_{c ≠ 0} Σ_{m,n} b̄_m b_n S(m, n; |c|) [Q ∣ c] c^{−2} Ψ_1(4π√(mn)/|c|)
  = Σ_{c ≠ 0} [Q ∣ c] c^{−2} Φ_b(|c|)`  (`sum_intKloosterman_gamma0Weight_eq`),

and summing the bound for one modulus over `c ≡ 0 (mod Q)` with `Σ_{Q∣c} |c|^{−s} = Q^{−s} Z_s`
(`tsum_dvd_natAbs_rpow`):

`|Σ_c …| ≤ (P K N^{1+2δ} Q^{−1−δ/2} Z_{1+δ/2} + P₃ K² e^{−K²/2}(N² Q^{−2} Z_2 + N³ Q^{−3} Z_3)) Σ|a|²`

(`exists_norm_tsum_kloosterman_part_le`).
-/

open MeasureTheory Set Filter Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open KuznetsovSeparation KuznetsovGauss RHTower.Sieve

noncomputable section

/-- `Z_s = Σ_{k ∈ ℤ} |k|^{−s}` (with `0^{−s} = 0`). -/
def intZeta (s : ℝ) : ℝ := ∑' k : ℤ, (k.natAbs : ℝ) ^ (-s)

theorem summable_natAbs_rpow {s : ℝ} (hs : 1 < s) :
    Summable fun k : ℤ => (k.natAbs : ℝ) ^ (-s) :=
  (Real.summable_abs_int_rpow hs).congr fun k => by rw [Nat.cast_natAbs, Int.cast_abs]

theorem intZeta_nonneg (s : ℝ) : 0 ≤ intZeta s := tsum_nonneg fun k => by positivity

/-- The indicator `[Q ∣ c] |c|^{−s}`. -/
def dvdRpow (Q : ℕ) (s : ℝ) (c : ℤ) : ℝ := if ((c : ZMod Q)) = 0 then (c.natAbs : ℝ) ^ (-s) else 0

theorem dvdRpow_nonneg (Q : ℕ) (s : ℝ) (c : ℤ) : 0 ≤ dvdRpow Q s c := by
  unfold dvdRpow; split_ifs <;> positivity

/-- `Σ_{Q ∣ c} |c|^{−s} = Q^{−s} Z_s`. -/
theorem summable_and_tsum_dvdRpow {Q : ℕ} (hQ : 1 ≤ Q) {s : ℝ} (hs : 1 < s) :
    Summable (dvdRpow Q s) ∧ ∑' c : ℤ, dvdRpow Q s c = (Q : ℝ) ^ (-s) * intZeta s := by
  have hsum : Summable (dvdRpow Q s) :=
    (summable_natAbs_rpow hs).of_nonneg_of_le (dvdRpow_nonneg Q s) fun c => by
      unfold dvdRpow
      split_ifs
      · exact le_rfl
      · positivity
  refine ⟨hsum, ?_⟩
  have hQ0 : (Q : ℤ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  have hinj : Function.Injective (fun k : ℤ => (Q : ℤ) * k) := mul_right_injective₀ hQ0
  have hsupp : Function.support (dvdRpow Q s) ⊆ Set.range (fun k : ℤ => (Q : ℤ) * k) := by
    intro c hc
    rw [Function.mem_support, dvdRpow] at hc
    split_ifs at hc with h
    · obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd c Q).1 h
      exact ⟨k, hk.symm⟩
    · exact absurd rfl hc
  rw [← hinj.tsum_eq hsupp, intZeta, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have h0 : (((Q : ℤ) * k : ℤ) : ZMod Q) = 0 := by push_cast; simp
  simp only [dvdRpow]
  rw [if_pos h0, Int.natAbs_mul, Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
  simp

/-! ## The terms of the Kloosterman part -/

theorem sqrt_div_sq_eq (x : ℝ) (c : ℤ) :
    Real.sqrt (x / (c : ℝ) ^ 2) = Real.sqrt x / (c.natAbs : ℝ) := by
  rw [Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq_eq_abs, Nat.cast_natAbs, Int.cast_abs]

theorem sum_intKloosterman_gamma0Weight_eq (Q : ℕ) (N : ℕ) (K : ℝ) (b : ℕ → ℂ) {c : ℤ} (hc : c ≠ 0)
    [NeZero c.natAbs] :
    ∑ k ∈ Finset.Ioc N (N + N), ∑ l ∈ Finset.Ioc N (N + N),
        conj (b k) * b l * (intKloosterman k l c * gamma0Weight Q K k l c) =
      (if ((c : ZMod Q)) = 0 then (1 : ℂ) else 0) * ((((c.natAbs : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) *
        modulusForm c.natAbs N K b := by
  classical
  rw [modulusForm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hint : intKloosterman k l c = kloostermanSum c.natAbs (k : ZMod c.natAbs) (l : ZMod c.natAbs) := by
    rw [intKloosterman, dif_neg hc]
    simp
  have hsq : (((c : ℝ) ^ 2) ^ (-(1 : ℝ))) = ((c.natAbs : ℝ) ^ 2)⁻¹ := by
    rw [Real.rpow_neg_one, Nat.cast_natAbs, Int.cast_abs, sq_abs]
  rw [hint, gamma0Weight, hsq, sqrt_div_sq_eq, mul_div_assoc]
  ring

theorem norm_sum_intKloosterman_gamma0Weight_le (Q : ℕ) (N : ℕ) (K : ℝ) (b : ℕ → ℂ) {c : ℤ}
    (hc : c ≠ 0) [NeZero c.natAbs] :
    ‖∑ k ∈ Finset.Ioc N (N + N), ∑ l ∈ Finset.Ioc N (N + N),
        conj (b k) * b l * (intKloosterman k l c * gamma0Weight Q K k l c)‖ ≤
      (if ((c : ZMod Q)) = 0 then 1 else 0) * (((c.natAbs : ℝ) ^ 2)⁻¹ * ‖modulusForm c.natAbs N K b‖) := by
  rw [sum_intKloosterman_gamma0Weight_eq Q N K b hc, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  split_ifs <;> simp

/-! ## Summing over the moduli -/

/-- **The Kloosterman part of the `Γ₀(Q)` geometric side.** -/
theorem exists_norm_tsum_kloosterman_part_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ P P₃ : ℝ, 0 ≤ P ∧ 0 ≤ P₃ ∧ ∀ (Q : ℕ), 1 ≤ Q → ∀ (N : ℕ), 1 ≤ N → ∀ (K : ℝ), 1 ≤ K →
      ∀ (a : ℕ → ℂ),
        (Summable fun c : ℤ => ∑ k ∈ Finset.Ioc N (N + N), ∑ l ∈ Finset.Ioc N (N + N),
          conj (gamma0Coeff a k) * gamma0Coeff a l *
            (intKloosterman k l c * gamma0Weight Q K k l c)) ∧
        ‖∑' c : ℤ, ∑ k ∈ Finset.Ioc N (N + N), ∑ l ∈ Finset.Ioc N (N + N),
            conj (gamma0Coeff a k) * gamma0Coeff a l *
              (intKloosterman k l c * gamma0Weight Q K k l c)‖ ≤
          (P * K * (N : ℝ) ^ (1 + 2 * δ) * ((Q : ℝ) ^ (-(1 + δ / 2)) * intZeta (1 + δ / 2)) +
            P₃ * K ^ 2 * Real.exp (-K ^ 2 / 2) *
              ((N : ℝ) ^ 2 * ((Q : ℝ) ^ (-(2 : ℝ)) * intZeta 2) +
                (N : ℝ) ^ 3 * ((Q : ℝ) ^ (-(3 : ℝ)) * intZeta 3))) *
            ∑ k ∈ Finset.Ioc N (N + N), ‖a k‖ ^ 2 := by
  obtain ⟨P, P₃, hP, hP₃, hmod⟩ := exists_modulus_bound_gamma0 hδ hδ1
  refine ⟨P, P₃, hP, hP₃, fun Q hQ N hN K hK a => ?_⟩
  set A := ∑ k ∈ Finset.Ioc N (N + N), ‖a k‖ ^ 2
  have hA : 0 ≤ A := Finset.sum_nonneg fun k _ => by positivity
  set F : ℤ → ℂ := fun c => ∑ k ∈ Finset.Ioc N (N + N), ∑ l ∈ Finset.Ioc N (N + N),
    conj (gamma0Coeff a k) * gamma0Coeff a l * (intKloosterman k l c * gamma0Weight Q K k l c)
  set s := 1 + δ / 2
  have hs : 1 < s := by simp only [s]; linarith
  set α₁ := P * K * (N : ℝ) ^ (1 + 2 * δ)
  set α₂ := P₃ * K ^ 2 * Real.exp (-K ^ 2 / 2) * (N : ℝ) ^ 2
  set α₃ := P₃ * K ^ 2 * Real.exp (-K ^ 2 / 2) * (N : ℝ) ^ 3
  have hα₁ : 0 ≤ α₁ := by positivity
  have hα₂ : 0 ≤ α₂ := by positivity
  have hα₃ : 0 ≤ α₃ := by positivity
  set g : ℤ → ℝ := fun c => (α₁ * dvdRpow Q s c + α₂ * dvdRpow Q 2 c + α₃ * dvdRpow Q 3 c) * A
  obtain ⟨hs1, hs1'⟩ := summable_and_tsum_dvdRpow hQ hs
  obtain ⟨hs2, hs2'⟩ := summable_and_tsum_dvdRpow hQ (s := 2) (by norm_num)
  obtain ⟨hs3, hs3'⟩ := summable_and_tsum_dvdRpow hQ (s := 3) (by norm_num)
  have hg : Summable g :=
    (((hs1.mul_left α₁).add (hs2.mul_left α₂)).add (hs3.mul_left α₃)).mul_right A
  have hFg : ∀ c, ‖F c‖ ≤ g c := by
    intro c
    by_cases hc : c = 0
    · subst hc
      have : F 0 = 0 := by
        simp [F, intKloosterman]
      rw [this, norm_zero]
      have := dvdRpow_nonneg Q s 0
      have := dvdRpow_nonneg Q 2 0
      have := dvdRpow_nonneg Q 3 0
      positivity
    · haveI : NeZero c.natAbs := ⟨Int.natAbs_ne_zero.2 hc⟩
      refine (norm_sum_intKloosterman_gamma0Weight_le Q N K _ hc).trans ?_
      have hb := hmod c.natAbs N hN K hK a
      have hc0 : (0 : ℝ) < c.natAbs := by exact_mod_cast Nat.pos_of_ne_zero (Int.natAbs_ne_zero.2 hc)
      have e2 : ((c.natAbs : ℝ) ^ 2)⁻¹ = (c.natAbs : ℝ) ^ (-(2 : ℝ)) := by
        rw [Real.rpow_neg hc0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have e3 : ((c.natAbs : ℝ) ^ 3)⁻¹ = (c.natAbs : ℝ) ^ (-(3 : ℝ)) := by
        rw [Real.rpow_neg hc0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [e2, e3] at hb
      simp only [g, dvdRpow]
      split_ifs with hq
      · rw [one_mul, e2]
        refine hb.trans (le_of_eq ?_)
        simp only [α₁, α₂, α₃, s]
        ring
      · simp
  have hFsum : Summable fun c => ‖F c‖ := hg.of_nonneg_of_le (fun c => norm_nonneg _) hFg
  refine ⟨hFsum.of_norm, ?_⟩
  calc ‖∑' c : ℤ, F c‖ ≤ ∑' c : ℤ, ‖F c‖ := norm_tsum_le_tsum_norm hFsum
    _ ≤ ∑' c : ℤ, g c := hFsum.tsum_le_tsum hFg hg
    _ = (α₁ * ((Q : ℝ) ^ (-s) * intZeta s) + α₂ * ((Q : ℝ) ^ (-(2 : ℝ)) * intZeta 2) +
          α₃ * ((Q : ℝ) ^ (-(3 : ℝ)) * intZeta 3)) * A := by
        simp only [g]
        rw [tsum_mul_right, ((hs1.mul_left α₁).add (hs2.mul_left α₂)).tsum_add (hs3.mul_left α₃),
          (hs1.mul_left α₁).tsum_add (hs2.mul_left α₂), tsum_mul_left, tsum_mul_left, tsum_mul_left,
          hs1', hs2', hs3']
    _ = _ := by simp only [α₁, α₂, α₃, s]; ring

end

end GaloisForLFunctions.RHTower.DeckPointPair
