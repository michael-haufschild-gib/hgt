import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedContinuation.PartitionPoles
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedContinuation.HarmonicSupport

/-!
# Unbounded critical clock harmonics

Insertion of a contracted clock phase takes one finite difference of the
radial residues. Positivity keeps every iterated difference geometrically
small, so the nonzero real residue rules out a vanishing harmonic tail.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedContinuation

open Filter
open scoped Topology ComplexConjugate

private def phase (t : ExceptionalTime) (j : ℕ) (x : Label t j) :=
  balancedHeat t j ⟨0,Real.pi/(logRadix t j).val⟩ x

private theorem phase_norm (t : ExceptionalTime) (j : ℕ) (x : Label t j) : ‖phase t j x‖ = 1 := by
  simp [phase,balancedHeat,norm_heat]

private theorem harmonic_heat (t : ExceptionalTime) (j k : ℕ) (β : ℝ) (x : Label t j) :
    balancedHeat t j (ray t j (k:ℤ) β) x = balancedHeat t j (β:ℂ) x * (phase t j x)^k := by
  let u : ℂ := ⟨0,Real.pi/(logRadix t j).val⟩
  let E : ℂ := (energy (⟨x.val.val,x.property⟩:ℕ+):ℝ)
  have h : ray t j (k:ℤ) β = (β:ℂ)+(k:ℂ)*u := by
    apply Complex.ext <;> simp [ray,clockPoint,u,Complex.mul_re,Complex.mul_im]
  change Complex.exp (-(ray t j (k:ℤ) β)*E) = Complex.exp (-(β:ℂ)*E)*(Complex.exp (-u*E))^k
  rw [← Complex.exp_nat_mul,← Complex.exp_add,h]
  congr 1
  ring

private def residue (t : ExceptionalTime) (j k : ℕ) :=
  numerator t j (point t j (k:ℤ))/(2*((logRadix t j).val:ℂ))

private def packet (t : ExceptionalTime) (j : ℕ) (a : ℂ) (m k : ℕ) (β : ℝ) (x : Label t j) :=
  balancedHeat t j (β:ℂ) x*(phase t j x)^k*(1-a*phase t j x)^m

private def reading (t : ExceptionalTime) (j : ℕ) (a : ℂ) (m k : ℕ) (β : ℝ) :=
  ((β-1/2:ℝ):ℂ)*∑' x, packet t j a m k β x

private theorem packet_bound (t : ExceptionalTime) (j : ℕ) {a : ℂ} {r : ℝ}
    (h : ∀ x, ‖1-a*phase t j x‖ ≤ r) (m k : ℕ) (β : ℝ) (x : Label t j) :
    ‖packet t j a m k β x‖ ≤ r^m*‖balancedHeat t j (β:ℂ) x‖ := by
  rw [packet,norm_mul,norm_mul,norm_pow,norm_pow,phase_norm,one_pow,mul_one,mul_comm]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (h x) m) (norm_nonneg _)

private theorem packet_sum (t : ExceptionalTime) (j : ℕ) {a : ℂ} {r : ℝ}
    (h : ∀ x, ‖1-a*phase t j x‖ ≤ r) (m k : ℕ) (β : {b : ℝ // 1/2 < b}) :
    Summable (fun x => ‖packet t j a m k β.val x‖) :=
  (((balanced_heat_summable_iff t j (β.val:ℂ)).mpr β.property).mul_left (r^m)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (packet_bound t j h m k β.val)

private theorem reading_succ (t : ExceptionalTime) (j : ℕ) {a : ℂ} {r : ℝ}
    (h : ∀ x, ‖1-a*phase t j x‖ ≤ r) (m k : ℕ) (β : {b : ℝ // 1/2 < b}) :
    reading t j a (m+1) k β.val = reading t j a m k β.val-a*reading t j a m (k+1) β.val := by
  have hw (x : Label t j) : packet t j a (m+1) k β.val x =
      packet t j a m k β.val x-a*packet t j a m (k+1) β.val x := by
    simp only [packet,pow_succ]
    ring
  unfold reading
  rw [tsum_congr hw,Summable.tsum_sub (packet_sum t j h m k β).of_norm
    ((packet_sum t j h m (k+1) β).of_norm.mul_left a),tsum_mul_left]
  ring

private theorem reading_limit (t : ExceptionalTime) (j : ℕ) {a : ℂ} {r : ℝ}
    (h : ∀ x, ‖1-a*phase t j x‖ ≤ r) (m k : ℕ) :
    Tendsto (reading t j a m k) (𝓝[>] (1/2:ℝ)) (𝓝 (iterateMoments a (residue t j) m k)) := by
  induction m generalizing k with
  | zero =>
    have hlim := radial_residue t j (k:ℤ)
    apply hlim.congr
    intro β
    simp only [reading,packet,pow_zero,mul_one,← harmonic_heat,balancedPartition]
  | succ m ih =>
    apply ((ih k).sub ((ih (k+1)).const_mul a)).congr'
    filter_upwards [self_mem_nhdsWithin] with β hβ
    exact (reading_succ t j h m k ⟨β,hβ⟩).symm

private theorem reading_bound (t : ExceptionalTime) (j : ℕ) {a : ℂ} {r : ℝ}
    (h : ∀ x, ‖1-a*phase t j x‖ ≤ r) (m k : ℕ) (β : {b : ℝ // 1/2 < b}) :
    ‖reading t j a m k β.val‖ ≤ r^m*‖((β.val-1/2:ℝ):ℂ)*balancedPartition t j (β.val:ℂ)‖ := by
  have hb := packet_sum t j h m k β
  have hs := (balanced_heat_summable_iff t j (β.val:ℂ)).mpr β.property
  have hu := hb.tsum_le_tsum (packet_bound t j h m k β.val) (hs.mul_left (r^m))
  rw [tsum_mul_left] at hu
  have hsum := (norm_tsum_le_tsum_norm hb).trans hu
  have hpos : 0 ≤ balancedMass t j β.val := tsum_nonneg (fun _ => norm_nonneg _)
  have hmass : ‖balancedPartition t j (β.val:ℂ)‖ = balancedMass t j β.val := by
    rw [balanced_partition_real,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hpos]
  rw [reading,norm_mul,norm_mul,hmass]
  calc _ ≤ ‖((β.val-1/2:ℝ):ℂ)‖*(r^m*balancedMass t j β.val) := mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
       _ = _ := by ring

private theorem decaying_columns (t : ExceptionalTime) (j : ℕ) :
    ∃ a : ℂ, ∀ k, Tendsto (fun m => ‖iterateMoments a (residue t j) m k‖) atTop (𝓝 0) := by
  obtain ⟨A,hA,c,hc,hcone⟩ := balanced_resonant_cone t j
  let a := (c:ℂ)*A
  let r := Real.sqrt (1-c^2)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hlt : r < 1 := (Real.sqrt_lt' zero_lt_one).mpr (by nlinarith only [sq_pos_of_pos hc])
  have hcontract (x : Label t j) : ‖1-a*phase t j x‖ ≤ r := by
    have hu : ‖A*phase t j x‖ = 1 := by rw [norm_mul,hA,phase_norm,one_mul]
    have he := hcone 0 x
    have hz : ‖balancedHeat t j ((0:ℝ):ℂ) x‖ = 1 := by simp [balancedHeat,norm_heat]
    rw [hz,mul_one] at he
    simpa only [a,mul_assoc] using unit_sector_contract hc hu he
  have hz (β : ℝ) : ray t j 0 β = (β:ℂ) := by apply Complex.ext <;> simp [ray,clockPoint]
  have h₀ := (radial_residue t j 0).norm
  simp only [hz] at h₀
  refine ⟨a,fun k => ?_⟩
  have hbound (m : ℕ) : ‖iterateMoments a (residue t j) m k‖ ≤ r^m*‖residue t j 0‖ := by
    apply le_of_tendsto_of_tendsto ((reading_limit t j hcontract m k).norm) (h₀.const_mul (r^m))
    filter_upwards [self_mem_nhdsWithin] with β hβ
    exact reading_bound t j hcontract m k ⟨β,hβ⟩
  apply squeeze_zero (fun m => norm_nonneg _) hbound
  simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hr hlt).mul_const ‖residue t j 0‖

/-- Every frequency cutoff is exceeded by a positive integer harmonic with a genuine simple pole. -/
theorem unbounded_simple_poles (t : ExceptionalTime) (j K : ℕ) :
    ∃ k : ℕ, K < k ∧ meromorphicOrderAt (continuation t j) (point t j (k:ℤ)) = (-1:ℤ) := by
  obtain ⟨a,ha⟩ := decaying_columns t j
  have h₀ := (clock_pole_iff t j 0).mp (first_clock_poles t j ⟨0,Or.inl rfl⟩)
  have hR : residue t j 0 ≠ 0 := div_ne_zero h₀ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr (logRadix t j).property.ne'))
  obtain ⟨k,hk,hn⟩ := unbounded_of_decaying_columns a (residue t j) ha hR (K+1)
  refine ⟨k,hk,(clock_pole_iff t j (k:ℤ)).mpr ?_⟩
  intro hz
  exact hn (by rw [residue,hz,zero_div])

/-- Reality of the heat energies pairs the two opposite clock residues. -/
theorem conjugate_numerators (t : ExceptionalTime) (j : ℕ) (k : ℤ) :
    numerator t j (point t j (-k)) = conj (numerator t j (point t j k)) := by
  have he : point t j (-k) = conj (point t j k) := by
    apply Complex.ext <;> simp [clockPoint, Complex.conj_re, Complex.conj_im]
  rw [he]
  simp only [numerator,firstHeat,correction,balancedHeat,heat,map_add,map_sum,Complex.conj_tsum,
    map_sub,map_mul,← Complex.exp_conj,map_neg,Complex.conj_ofReal]

/-- Arbitrarily high conjugate pairs of simple poles lie on the isometry line. -/
theorem unbounded_pole_pairs (t : ExceptionalTime) (j K : ℕ) :
    ∃ k : ℕ, K < k ∧
      meromorphicOrderAt (continuation t j) (point t j (k:ℤ)) = (-1:ℤ) ∧
      meromorphicOrderAt (continuation t j) (point t j (-(k:ℤ))) = (-1:ℤ) := by
  obtain ⟨k,hk,hp⟩ := unbounded_simple_poles t j K
  refine ⟨k,hk,hp,(clock_pole_iff t j (-(k:ℤ))).mpr ?_⟩
  rw [conjugate_numerators,ne_eq,map_eq_zero]
  exact (clock_pole_iff t j (k:ℤ)).mp hp

#print axioms unbounded_simple_poles
#print axioms conjugate_numerators
#print axioms unbounded_pole_pairs

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedContinuation
