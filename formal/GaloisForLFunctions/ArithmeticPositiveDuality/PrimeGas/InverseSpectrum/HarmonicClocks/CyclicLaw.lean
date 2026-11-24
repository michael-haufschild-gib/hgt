import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Fejer
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RapidZeros.Transport

/-! # A cyclic average of prime-block insertions -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

private theorem insertedMass_one (μ : ℕ+ → ℝ) (n : ℕ+) : insertedMass 1 μ n = μ n := by
  simpa only [one_mul] using insertedMass_at 1 n μ

/-- A fraction δ of the seed and equal shares of its first r multiplicative translates. -/
def cyclicMass (r a : ℕ+) (δ : ℝ) (μ : ℕ+ → ℝ) (n : ℕ+) :=
  δ*μ n+((1-δ)/(r.val:ℝ))*(∑ k ∈ Finset.range r.val, insertedMass (a^k) μ n)

private theorem cyclic_dominates (r a : ℕ+) {δ : ℝ} (hδ : δ ≤ 1) {μ : ℕ+ → ℝ}
    (hμ : ∀ n, 0 ≤ μ n) (n : ℕ+) : retentionCeiling r δ*μ n ≤ cyclicMass r a δ μ n := by
  have hs := Finset.single_le_sum (f := fun k => insertedMass (a^k) μ n)
    (fun k _ => insertedMass_nonneg (a^k) hμ n) (Finset.mem_range.mpr r.pos)
  rw [pow_zero,insertedMass_one] at hs
  unfold retentionCeiling cyclicMass
  rw [add_mul]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (div_nonneg (sub_nonneg.mpr hδ) (Nat.cast_nonneg _)))

def cyclicExterior (r a : ℕ+) (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) (ρ : ExteriorLaw) : ExteriorLaw := by
  have hρ : HasSum ρ.val 1 := Equiv.pnatEquivNat.symm.hasSum_iff.mp ρ.property.2.1
  have hq := retentionCeiling_pos r hδ hδ'
  have hd := cyclic_dominates r a hδ' ρ.property.1
  have hs := hasSum_sum (s := Finset.range r.val) (fun k _ => insertedMass_hasSum (a^k) hρ)
  have h := (hρ.mul_left δ).add (hs.mul_left ((1-δ)/(r.val:ℝ)))
  have he : δ*1+((1-δ)/(r.val:ℝ))*(∑ _ ∈ Finset.range r.val, (1:ℝ)) = 1 := by
    simp [show (r.val:ℝ) ≠ 0 by exact_mod_cast r.ne_zero]
  rw [he] at h
  exact ⟨cyclicMass r a δ ρ.val,fun n => (mul_nonneg hq.le (ρ.property.1 n)).trans (hd n),
    Equiv.pnatEquivNat.symm.hasSum_iff.mpr h,
    fun ht => exterior_mean_of_dominates ρ hq hd ((labelMean_summable_iff _).mpr ht)⟩

def cyclicWave (r a : ℕ+) (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) (v : MissingWave) :=
  lawOmission (cyclicExterior r a δ hδ hδ' (exteriorLaw v))

theorem cyclic_probability (r a : ℕ+) {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) (v : MissingWave) :
    occupationProbability (cyclicWave r a δ hδ hδ' v) = cyclicMass r a δ (occupationProbability v) :=
  lawOmission_probability _

/-- Below the first inserted block exactly the unshifted fraction of the seed remains. -/
theorem cyclic_below (r a : ℕ+) {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) (v : MissingWave)
    (n : ℕ+) (hn : (n:ℕ) < a.val) :
    occupationProbability (cyclicWave r a δ hδ hδ' v) n = retentionCeiling r δ*occupationProbability v n := by
  rw [cyclic_probability,cyclicMass,Finset.sum_eq_single 0,pow_zero,insertedMass_one,retentionCeiling,add_mul]
  · intro k _ hk
    apply insertedMass_below
    obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    change (n:ℕ) < (a.val)^(d+1)
    rw [pow_succ']
    exact hn.trans_le (Nat.le_mul_of_pos_right _ (pow_pos a.pos _))
  · exact fun h => (h (Finset.mem_range.mpr r.pos)).elim

private theorem splitPhase_label_pow (a : ℕ+) (t : ℝ) (k : ℕ) : splitPhase t (a^k) = splitPhase t a ^ k := by
  induction k with
  | zero => simp [splitPhase,heat,energy]
  | succ k ih =>
    rw [pow_succ,pow_succ,splitPhase,heat_mul]
    exact congrArg (fun z => z*splitPhase t a) ih

/-- The cyclic insertion acts on the composition response by its clock polynomial. -/
theorem cyclic_response (r a : ℕ+) {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) (v : MissingWave) (t : ℝ) :
    compositionResponse (cyclicWave r a δ hδ hδ' v) (criticalTime t) =
      ((δ:ℂ)+(((1-δ)/(r.val:ℝ):ℝ):ℂ)*clockPolynomial r.val (splitPhase t a))*
        compositionResponse v (criticalTime t) := by
  let c := (1-δ)/(r.val:ℝ)
  have hs := hasSum_sum (s := Finset.range r.val) (fun k _ => criticalTerms_hasSum (insertedWave (a^k) v) t)
  have h := ((criticalTerms_hasSum v t).mul_left (δ:ℂ)).add (hs.mul_left (c:ℂ))
  have he := (criticalTerms_hasSum (cyclicWave r a δ hδ hδ' v) t).unique (h.congr_fun (fun n => by
    simp only [cyclic_probability,cyclicMass,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_sum,
      insertedWave_probability,← Finset.sum_mul,c]
    ring))
  rw [he]
  have hk (k : ℕ) : heat (2*criticalTime t-1) (a^k) = splitPhase t a^k := splitPhase_label_pow a t k
  simp only [inserted_response,hk,← Finset.sum_mul,clockPolynomial,c]
  ring

#print axioms cyclic_probability
#print axioms cyclic_below
#print axioms cyclic_response

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
