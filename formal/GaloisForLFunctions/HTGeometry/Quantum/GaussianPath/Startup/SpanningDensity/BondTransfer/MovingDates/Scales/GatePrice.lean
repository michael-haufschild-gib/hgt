import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.CutCounts.ExcessCharge
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.Calibration.SmallAngles

/-! # Price of marked triples after accounting for crossed edges -/

open Filter Finset Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open FixedHorizon WeakBondDeficit RepeatedGates.PhysicalBlocks
open RepeatedGates.PhysicalBlocks.CollectiveSignals
noncomputable section

/-- At reciprocal date 1/j, the boundary cost grows at most as j¹⁹³
whereas the marked triples force order j²⁰⁰ extra gates. For later
dates the charge per triple grows at least as the eighth power of time. -/
theorem moving_gate_price {c A : ℝ} (hc : 0<c) (hA : 0≤A) :
    ∃ b>0, ∀ᶠ j : ℕ in atTop, ∀ (n : ℕ) (ω : PathPauliDisorder) (B t δ w : ℝ),
      let u := pathPauliDisorderShell ω n
      let s := 1/(j:ℝ)
      0≤B → (∀ l, |u l|≤B) → 3348*t*B≤1 → s≤t → t≤1 →
      ((weakEdges u (s^7)).card:ℝ)≤A*(j:ℝ)^193 →
      missedBonds n (j^80) (s^8) ω=∅ →
      0≤δ → δ≤t/10000 → (j:ℝ)^208≤w →
      c*w≤((goodBoxes (1/sqrt 2) δ ω ((n+1)/4)).card:ℝ) →
      ∀ k : ℕ, HasProjectiveCircuitApproximation (n+2) (1/4) k (unitaryEvolution (pathHamiltonian u) t) →
        ((n+1:ℕ):ℝ)+b*w*t^8<(k:ℝ) := by
  let b := c/(4*546*2^8)
  have hb : 0<b := by dsimp only [b]; positivity
  obtain ⟨J,hJ⟩ := exists_nat_gt ((A+5000)/b)
  refine ⟨b,hb,?_⟩
  filter_upwards [eventually_ge_atTop J,eventually_ge_atTop (576:ℕ)] with j hjJ hj
  intro n ω B t δ w u s hB hcap hsmall ht ht₁ hw hm hδ hδt hweight hboxes k hfit
  have hJpos : 0<(j:ℝ) := by exact_mod_cast (show 0<j by omega)
  have hj₁ : 1≤(j:ℝ) := by exact_mod_cast (show 1≤j by omega)
  have hs : 0<s := one_div_pos.mpr hJpos
  have htpos := hs.trans_le ht
  have hsin := short_sine (show t∈Ioc (0:ℝ) 1 from ⟨htpos,ht₁⟩)
  have hsin₂ := pow_le_pow_left₀ (half_pos htpos).le hsin 2
  have herr : 252* |t| * δ≤(sin t)^2/4 := by
    rw [abs_of_pos htpos]
    linarith only [mul_le_mul_of_nonneg_left hδt htpos.le,hsin₂,sq_nonneg t]
  have hweak : 36* |t| * s^8≤(t*s^7)/16 := by
    rw [abs_of_pos htpos]
    have h₁ : 576*s≤1 := by
      dsimp only [s]; rw [mul_one_div,div_le_one hJpos]; exact_mod_cast hj
    linarith only [mul_le_mul_of_nonneg_left h₁ (mul_nonneg htpos.le (pow_nonneg hs.le 7))]
  have hpack : 16<((17*j^8:ℕ):ℝ)*(t*s^7) := by
    have he : ((17*j^8:ℕ):ℝ)*(s*s^7)=17 := by
      push_cast
      dsimp only [s]
      field_simp
    linarith only [he,mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht (pow_nonneg hs.le 7))
      (show (0:ℝ)≤(17*j^8:ℕ) from Nat.cast_nonneg _)]
  obtain ⟨z,hz,C,hC,hf⟩ := hfit
  have hh := physical_excess_charge ω C htpos (pow_pos hs 7) hB hcap hsmall (j^80) (17*j^8)
    hpack hweak hδ (sq_pos_of_pos ((half_pos htpos).trans_le hsin)) herr z hz hf
  dsimp only at hh
  rw [hm,Finset.card_empty,add_zero] at hh
  push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] at hh
  have hgain := mul_le_mul hboxes (pow_le_pow_left₀ (half_pos htpos).le hsin 8)
    (pow_nonneg (half_pos htpos).le _) (Nat.cast_nonneg _)
  have hbase : (j:ℝ)^200=(j:ℝ)^208*s^8 := by
    dsimp only [s]
    field_simp
  have h₀ := mul_le_mul hweight (pow_le_pow_left₀ hs.le ht 8) (pow_nonneg hs.le 8)
    ((pow_nonneg hJpos.le 208).trans hweight)
  rw [←hbase] at h₀
  have hcoef := (div_lt_iff₀ hb).mp (hJ.trans_le (Nat.cast_le.mpr hjJ))
  have hdom : (A+5000)*(j:ℝ)^193<b*(j:ℝ)^200 := calc
    _ < ((j:ℝ)*b)*(j:ℝ)^193 := mul_lt_mul_of_pos_right hcoef (pow_pos hJpos _)
    _ = b*(j:ℝ)^194 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hj₁ (by decide : 194≤200)) hb.le
  have hp (m : ℕ) (hm : m≤193) := pow_le_pow_right₀ hj₁ hm
  have hcost : (C.gateCount:ℝ)≤k := Nat.cast_le.mpr hC
  have hu : 1≤(j:ℝ)^193 := one_le_pow₀ hj₁
  have he : c=4*546*2^8*b := by dsimp only [b]; ring
  have hpos : 0≤b*(w*t^8) := (mul_nonneg (by linarith only [hA] : 0≤A+5000) (pow_nonneg hJpos.le 193)).trans
    (hdom.le.trans (mul_le_mul_of_nonneg_left h₀ hb.le))
  rw [he] at hgain
  change ((n+1:ℕ):ℝ)+b*w*t^8<(k:ℝ)
  push_cast only [Nat.cast_add,Nat.cast_one]
  linarith only [hh,hgain,hw,hcost,hdom,hpos,mul_le_mul_of_nonneg_left h₀ hb.le,hu,
    hp 96 (by decide),hp 16 (by decide),hp 80 (by decide)]

#print axioms moving_gate_price
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
