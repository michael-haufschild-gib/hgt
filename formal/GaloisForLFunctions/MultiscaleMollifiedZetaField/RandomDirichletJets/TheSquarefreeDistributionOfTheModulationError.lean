import GaloisForLFunctions.MultiscaleMollifiedZetaField.RandomDirichletJets.FractionalGradientsOfMultiplicativelyShiftedSections
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheConstantTermOfTheSquarefreeHarmonicDiagonal

/-!
# Distribution of the fractional modulation error on the critical Möbius row

Squaring the critical coefficients gives each mode the mass μ(n)²/n.
The symbol error is strictly increasing in the logarithmic frequency. A
quantile of the error is therefore an arithmetic cutoff, and its cumulative
mass inherits the explicit finite part of the squarefree harmonic diagonal.
-/

noncomputable section
open Finset Filter Topology MeasureTheory Complex
open GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
open _root_.RHTower.Sieve _root_.RHTower.SteinhausModel
namespace GaloisForLFunctions.MultiscaleMollifiedZetaField.RandomDirichletJets

/-- Mode error at fraction u of the cutoff's logarithmic bandwidth. -/
def modulationQuantile (s : ℝ) (M N : ℕ) (u : ℝ) :=
  (1+(u*Real.log N)/Real.log M)^s-1

/-- Squarefree critical mass of all modes below the specified symbol error. -/
def squarefreeModulationMass (s : ℝ) (M N : ℕ) (u : ℝ) : ℝ :=
  ∑ n ∈ (Icc 1 N).filter (fun n => fractionalModulationLoss s M n ≤ modulationQuantile s M N u),
    ((ArithmeticFunction.moebius n:ℤ):ℝ)^2/(n:ℝ)

private theorem quantile_le_cutoff {s u : ℝ} (hs : 0 < s) (hu : 0 ≤ u) {M N n : ℕ}
    (hM : 2 ≤ M) (hN : 1 ≤ N) (hn : 1 ≤ n) :
    fractionalModulationLoss s M n ≤ modulationQuantile s M N u ↔ (n:ℝ) ≤ (N:ℝ)^u := by
  have hL : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hN1 : (1:ℝ) ≤ N := Nat.one_le_cast.mpr hN
  have hn1 : (1:ℝ) ≤ n := Nat.one_le_cast.mpr hn
  have hN0 := zero_lt_one.trans_le hN1
  rw [fractionalModulationLoss,modulationQuantile,sub_le_sub_iff_right,
    Real.rpow_le_rpow_iff (add_nonneg zero_le_one (div_nonneg (Real.log_nonneg hn1) hL.le))
      (add_nonneg zero_le_one (div_nonneg (mul_nonneg hu (Real.log_nonneg hN1)) hL.le)) hs,
    add_le_add_iff_left,div_le_div_iff_of_pos_right hL,←Real.log_rpow hN0,
    Real.log_le_log_iff (zero_lt_one.trans_le hn1) (Real.rpow_pos_of_pos hN0 u)]

/-- Exact quantile mass throughout the entire range. The carrier and the
positive fractional order both disappear from this identity. -/
theorem squarefree_modulation_quantile (s : ℝ) (hs : 0 < s) {M N : ℕ}
    (hM : 2 ≤ M) (hN : 1 ≤ N) {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) :
    squarefreeModulationMass s M N u = harmonicMoebiusDiagonal ((N:ℝ)^u) := by
  have hN1 := (Nat.one_le_cast (α:=ℝ)).mpr hN
  have hle := Real.rpow_le_self_of_one_le hN1 hu.2
  have h0 := Real.rpow_nonneg (zero_le_one.trans hN1) u
  have he : (Icc 1 N).filter (fun n => fractionalModulationLoss s M n ≤ modulationQuantile s M N u) =
      Icc 1 ⌊(N:ℝ)^u⌋₊ := by
    ext n
    simp only [mem_filter,mem_Icc]
    constructor
    · rintro ⟨⟨hn,_⟩,ht⟩
      exact ⟨hn,(Nat.le_floor_iff h0).mpr ((quantile_le_cutoff hs hu.1 hM hN hn).mp ht)⟩
    · rintro ⟨hn,hcut⟩
      have hx := (Nat.le_floor_iff h0).mp hcut
      exact ⟨⟨hn,Nat.cast_le.mp (hx.trans hle)⟩,(quantile_le_cutoff hs hu.1 hM hN hn).mpr hx⟩
  rw [squarefreeModulationMass,he,harmonicMoebiusDiagonal]

/-- The error in the finite-part formula improves as the quantile recedes
from the stationary mode. The bound is uniform in both order and carrier. -/
theorem squarefree_modulation_quantile_finite_part {s : ℝ} (hs : 0 < s) {M N : ℕ}
    (hM : 2 ≤ M) (hN : 1 ≤ N) {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) :
    |squarefreeModulationMass s M N u - squarefreeDensity*(u*Real.log N)-squarefreeHarmonicConstant| ≤
      12*(N:ℝ)^(-(u/2)) := by
  have hN1 := (Nat.one_le_cast (α:=ℝ)).mpr hN
  have h := squarefree_harmonic_finite_part (Real.one_le_rpow hN1 hu.1)
  rw [Real.log_rpow (zero_lt_one.trans_le hN1),←Real.rpow_mul (zero_le_one.trans hN1)] at h
  rw [squarefree_modulation_quantile s hs hM hN hu]
  simpa only [show u*(-(1/2:ℝ))=-(u/2) by ring] using h

/-- At an interior fraction the unnormalized deviation from the uniform
quantile tends to (1-u) times the finite part of ζ(s)/ζ(2s). -/
theorem centered_squarefree_modulation_quantile (M N : ℕ → ℕ) (order : ℕ → ℝ)
    (hM : ∀ k, 2 ≤ M k) (hN : ∀ k, 1 ≤ N k) (hs : ∀ k, 0 < order k)
    (hcutoff : Tendsto N atTop atTop) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    Tendsto (fun k => squarefreeModulationMass (order k) (M k) (N k) u -
      u*harmonicMoebiusDiagonal (N k)) atTop (𝓝 ((1-u)*squarefreeHarmonicConstant)) := by
  have hNr := tendsto_natCast_atTop_atTop (R:=ℝ) |>.comp hcutoff
  let E (v : ℝ) (k : ℕ) := squarefreeModulationMass (order k) (M k) (N k) v -
    squarefreeDensity*(v*Real.log (N k))-squarefreeHarmonicConstant
  have herr (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) : Tendsto (E v) atTop (𝓝 0) := by
    have H := (tendsto_rpow_neg_atTop (show 0 < v/2 by positivity)).comp hNr
    have hb : Tendsto (fun k => 12*(N k:ℝ)^(-(v/2))) atTop (𝓝 0) := by
      simpa only [Function.comp_apply,mul_zero] using H.const_mul 12
    apply squeeze_zero_norm (fun k => ?_) hb
    simpa only [E,Real.norm_eq_abs] using squarefree_modulation_quantile_finite_part
      (hs k) (hM k) (hN k) (Set.mem_Icc.mpr ⟨hv.le,hv1⟩)
  have hfull (k : ℕ) : squarefreeModulationMass (order k) (M k) (N k) 1 =
      harmonicMoebiusDiagonal (N k) := by
    rw [squarefree_modulation_quantile _ (hs k) (hM k) (hN k) ⟨zero_le_one,le_rfl⟩,Real.rpow_one]
  have H := ((herr u hu hu1).sub ((herr 1 zero_lt_one le_rfl).const_mul u)).add
    (tendsto_const_nhds (x:=(1-u)*squarefreeHarmonicConstant))
  simpa only [mul_zero,sub_zero,zero_add] using H.congr (fun k => by dsimp only [E]; rw [hfull]; ring)

/-- At distance c/log N from the lower endpoint, the profile retains the
individual squarefree jumps through exp c, exactly at every admissible cutoff. -/
theorem microscopic_squarefree_modulation_quantile {s c : ℝ} (hs : 0 < s) {M N : ℕ}
    (hM : 2 ≤ M) (hN : 2 ≤ N) (hc : 0 ≤ c) (hcN : c ≤ Real.log N) :
    squarefreeModulationMass s M N (c/Real.log N) = harmonicMoebiusDiagonal (Real.exp c) := by
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [squarefree_modulation_quantile s hs hM (show 1 ≤ N by omega)
    ⟨div_nonneg hc hL.le,(div_le_one hL).mpr hcN⟩,Real.rpow_def_of_pos (by positivity : (0:ℝ)<N)]
  rw [show Real.log N*(c/Real.log N)=c by field_simp]

/-- Squared modulus of the critical coefficient at a single arithmetic mode. -/
def criticalMoebiusMass (n : ℕ) : ℝ := ((ArithmeticFunction.moebius n:ℤ):ℝ)^2/n

theorem criticalMoebiusMass_nonneg (n : ℕ) : 0 ≤ criticalMoebiusMass n :=
  div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- Actual critical Möbius coefficients in the random Dirichlet section. -/
def criticalMoebiusAmplitude (n : ℕ) : ℂ := ((((ArithmeticFunction.moebius n:ℤ):ℝ)/Real.sqrt n:ℝ):ℂ)

theorem criticalMoebiusAmplitude_norm_sq (n : ℕ) :
    ‖criticalMoebiusAmplitude n‖^2 = criticalMoebiusMass n := by
  rw [criticalMoebiusAmplitude,Complex.norm_real,Real.norm_eq_abs,sq_abs,div_pow,
    Real.sq_sqrt (Nat.cast_nonneg n),criticalMoebiusMass]

theorem harmonicMoebiusDiagonal_at_nat (N : ℕ) : harmonicMoebiusDiagonal N = ∑ n ∈ Icc 1 N, criticalMoebiusMass n := by
  simp only [harmonicMoebiusDiagonal,Nat.floor_natCast,criticalMoebiusMass]

theorem harmonicMoebiusDiagonal_pos_of_one_le {N : ℕ} (hN : 1 ≤ N) : 0 < harmonicMoebiusDiagonal N := by
  rw [harmonicMoebiusDiagonal_at_nat]
  have h := single_le_sum (f:=criticalMoebiusMass) (fun n _ => criticalMoebiusMass_nonneg n) (mem_Icc.mpr ⟨le_rfl,hN⟩)
  exact lt_of_lt_of_le (by norm_num [criticalMoebiusMass] : 0 < criticalMoebiusMass 1) h

/-- A uniform quantile error bound must pay for the stationary squarefree
atom. Conversely the finite part bounds every quantile discrepancy by a
constant times the same inverse harmonic mass, including at both ends. -/
theorem uniform_squarefree_quantile_discrepancy {s : ℝ} (hs : 0 < s) {M N : ℕ}
    (hM : 2 ≤ M) (hN : 1 ≤ N) :
    let H := harmonicMoebiusDiagonal N
    (∀ ε : ℝ, (∀ u ∈ Set.Icc (0:ℝ) 1,
      |squarefreeModulationMass s M N u / H - u| ≤ ε) → 1/H ≤ ε) ∧
    ∀ u ∈ Set.Icc (0:ℝ) 1, |squarefreeModulationMass s M N u / H - u| ≤
      (24+|squarefreeHarmonicConstant|)/H := by
  intro H
  have hH : 0 < H := harmonicMoebiusDiagonal_pos_of_one_le hN
  have hN1 : (1:ℝ) ≤ N := Nat.one_le_cast.mpr hN
  constructor
  · intro ε h
    have h0 := h 0 ⟨le_rfl,zero_le_one⟩
    rw [squarefree_modulation_quantile s hs hM hN ⟨le_rfl,zero_le_one⟩,Real.rpow_zero] at h0
    have hone : harmonicMoebiusDiagonal 1=1 := by norm_num [harmonicMoebiusDiagonal]
    rwa [hone,sub_zero,abs_of_nonneg (div_nonneg zero_le_one hH.le)] at h0
  · intro u hu
    let E := squarefreeModulationMass s M N u-squarefreeDensity*(u*Real.log N)-squarefreeHarmonicConstant
    let D := H-squarefreeDensity*Real.log N-squarefreeHarmonicConstant
    have hE : |E| ≤ 12 := (squarefree_modulation_quantile_finite_part hs hM hN hu).trans
      (by have hh := Real.rpow_le_one_of_one_le_of_nonpos hN1 (neg_nonpos.mpr (div_nonneg hu.1 zero_le_two));
          linarith only [hh])
    have hD : |D| ≤ 12 := (squarefree_harmonic_finite_part hN1).trans
      (by have hh := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num : -(1/2:ℝ) ≤ 0);
          linarith only [hh])
    have hid : squarefreeModulationMass s M N u/H-u =
        (E+(1-u)*squarefreeHarmonicConstant-u*D)/H := by
      dsimp only [E,D]; field_simp [hH.ne']; ring
    rw [hid,abs_div,abs_of_pos hH]
    apply div_le_div_of_nonneg_right _ hH.le
    have hc := abs_sub (E+(1-u)*squarefreeHarmonicConstant) (u*D)
    have ha := abs_add_le E ((1-u)*squarefreeHarmonicConstant)
    rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr hu.2)] at ha
    rw [abs_mul,abs_of_nonneg hu.1] at hc
    have hb := mul_le_mul_of_nonneg_right (show 1-u ≤ 1 by linarith only [hu.1]) (abs_nonneg squarefreeHarmonicConstant)
    have hd' := mul_le_mul_of_nonneg_right hu.2 (abs_nonneg D)
    linarith only [hc,ha,hb,hd',hE,hD]

/-- Relative mean-square modulation error for the unmodified critical Möbius row. -/
def relativeMoebiusModulationEnergy (s : ℝ) (M N : ℕ) :=
  (∫ ω, ‖fractionalModulationError s M N criticalMoebiusAmplitude ω‖^2 ∂steinhausMeasure) /
    harmonicMoebiusDiagonal N

private theorem quantile_nonneg {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u)
    {M N : ℕ} (hM : 2 ≤ M) (hN : 1 ≤ N) : 0 ≤ modulationQuantile s M N u := by
  have hL := Real.log_nonneg (Nat.one_le_cast.mpr hN)
  have hden := Real.log_nonneg (Nat.one_le_cast.mpr (show 1 ≤ M by omega))
  exact sub_nonneg.mpr (Real.one_le_rpow
    (by linarith only [div_nonneg (mul_nonneg hu hL) hden]) hs)

/-- The portion of the actual row above any symbol quantile forces a
lower bound on the error. The highest mode gives the upper bound. -/
theorem moebius_modulation_energy_sandwich {s : ℝ} (hs : 0 < s) {M N : ℕ}
    (hM : 2 ≤ M) (hN : 1 ≤ N) {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) :
    (modulationQuantile s M N u)^2*(harmonicMoebiusDiagonal N-squarefreeModulationMass s M N u)
      ≤ relativeMoebiusModulationEnergy s M N*harmonicMoebiusDiagonal N ∧
    relativeMoebiusModulationEnergy s M N ≤ (fractionalModulationLoss s M N)^2 := by
  let S := Icc 1 N
  let r (n : ℕ) := fractionalModulationLoss s M n
  let v := modulationQuantile s M N u
  let A := S.filter (fun n => r n ≤ v)
  have hD := harmonicMoebiusDiagonal_pos_of_one_le hN
  have he := fractional_modulation_energy s hM N criticalMoebiusAmplitude
  simp only [criticalMoebiusAmplitude_norm_sq] at he
  have hcomp : harmonicMoebiusDiagonal N-squarefreeModulationMass s M N u =
      ∑ n ∈ S \ A, criticalMoebiusMass n := by
    rw [harmonicMoebiusDiagonal_at_nat,sum_sdiff_eq_sub (show A ⊆ S from filter_subset _ _)]
    rfl
  constructor
  · rw [relativeMoebiusModulationEnergy,div_mul_cancel₀ _ hD.ne',he,hcomp,mul_sum]
    calc (∑ n ∈ S \ A, v^2*criticalMoebiusMass n) ≤ ∑ n ∈ S \ A, r n^2*criticalMoebiusMass n := by
           apply sum_le_sum
           intro n hn
           have hh := mem_sdiff.mp hn
           have hv : v ≤ r n := le_of_lt (lt_of_not_ge fun h => hh.2 (mem_filter.mpr ⟨hh.1,h⟩))
           exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (quantile_nonneg hs.le hu.1 hM hN) hv 2)
             (criticalMoebiusMass_nonneg n)
      _ ≤ ∑ n ∈ S, r n^2*criticalMoebiusMass n := sum_le_sum_of_subset_of_nonneg sdiff_subset
        (fun n _ _ => mul_nonneg (sq_nonneg _) (criticalMoebiusMass_nonneg n))
  · have H := (optimal_fractional_modulation_energy_iff hs.le hM hN _).mpr le_rfl criticalMoebiusAmplitude
    rw [relativeMoebiusModulationEnergy,div_le_iff₀ hD,harmonicMoebiusDiagonal_at_nat]
    simpa only [criticalMoebiusAmplitude_norm_sq] using H

theorem tendsto_squarefree_harmonic_diagonal_atTop (N : ℕ → ℕ) (hN : ∀ k, 1 ≤ N k) (hcutoff : Tendsto N atTop atTop) :
    Tendsto (fun k => harmonicMoebiusDiagonal (N k)) atTop atTop := by
  have hd : 0 < squarefreeDensity := by rw [squarefreeDensity_eq]; positivity
  have hl := Real.tendsto_log_atTop.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp hcutoff)
  refine tendsto_atTop.mpr fun b => ?_
  filter_upwards [hl.eventually_ge_atTop ((b-squarefreeHarmonicConstant+12)/squarefreeDensity)] with k hk
  have hN1 : (1:ℝ) ≤ N k := Nat.one_le_cast.mpr (hN k)
  have he := (abs_le.mp (squarefree_harmonic_finite_part hN1)).1
  have hb := (div_le_iff₀ hd).mp hk
  have hp := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num : -(1/2:ℝ) ≤ 0)
  change b-squarefreeHarmonicConstant+12 ≤ Real.log (N k)*squarefreeDensity at hb
  linarith only [he,hb,hp]

/-- For long sections the critical Möbius row itself detects the sharp
bandwidth threshold, even with only its random mean-square reading. -/
theorem relative_moebius_modulation_tendsto_zero_iff {s : ℝ} (hs : 0 < s) (M N : ℕ → ℕ)
    (hM : ∀ k, 2 ≤ M k) (hN : ∀ k, 1 ≤ N k) (hcutoff : Tendsto N atTop atTop) :
    Tendsto (fun k => relativeMoebiusModulationEnergy s (M k) (N k)) atTop (𝓝 0) ↔
    Tendsto (fun k => Real.log (N k)/Real.log (M k)) atTop (𝓝 0) := by
  let E (k : ℕ) := relativeMoebiusModulationEnergy s (M k) (N k)
  let H (k : ℕ) := harmonicMoebiusDiagonal (N k)
  let r (k : ℕ) := modulationQuantile s (M k) (N k) (1/2)
  have hn (k : ℕ) : 0 ≤ E k := div_nonneg (integral_nonneg fun _ => sq_nonneg _) (harmonicMoebiusDiagonal_pos_of_one_le (hN k)).le
  have hr (k : ℕ) : 0 ≤ r k := quantile_nonneg hs.le (by norm_num) (hM k) (hN k)
  have hb (k : ℕ) := moebius_modulation_energy_sandwich hs (hM k) (hN k)
    (u:=1/2) (Set.mem_Icc.mpr ⟨by norm_num,by norm_num⟩)
  constructor
  · intro h
    let D := (1-(1/2:ℝ))*squarefreeHarmonicConstant+1
    have hc := centered_squarefree_modulation_quantile M N (fun _ => s) hM hN (fun _ => hs) hcutoff
      (u:=1/2) (by norm_num) (by norm_num)
    have hupper := hc.eventually_le_const (show (1-(1/2:ℝ))*squarefreeHarmonicConstant < D by dsimp [D]; linarith)
    have hbig := (tendsto_squarefree_harmonic_diagonal_atTop N hN hcutoff).eventually_ge_atTop (4*D)
    have hstep : ∀ᶠ k in atTop, r k^2 ≤ 4*E k := by
      filter_upwards [hupper,hbig] with k hu hlarge
      have hlow : H k/4 ≤ H k-squarefreeModulationMass s (M k) (N k) (1/2) := by
        dsimp [H]; linarith only [hu,hlarge]
      have hh := (mul_le_mul_of_nonneg_left hlow (sq_nonneg (r k))).trans (hb k).1
      apply le_of_mul_le_mul_right (a:=H k) _ (harmonicMoebiusDiagonal_pos_of_one_le (hN k))
      change r k^2*(H k/4) ≤ E k*H k at hh
      linarith only [hh]
    have hsq : Tendsto (fun k => r k^2) atTop (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall fun k => sq_nonneg _) hstep (by simpa using h.const_mul 4)
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    have hr0 : Tendsto r atTop (𝓝 0) := by
      simpa only [Function.comp_def,Real.sqrt_sq (hr _),Real.sqrt_zero] using hsqrt
    have hrecover := ((tendsto_const_nhds (x:=(1:ℝ))).add hr0).rpow_const
      (p:=s⁻¹) (Or.inr (inv_nonneg.mpr hs.le))
    have heq (k : ℕ) : 2*((1+r k)^s⁻¹-1) = Real.log (N k)/Real.log (M k) := by
      let Q := ((1/2:ℝ)*Real.log (N k))/Real.log (M k)
      have h0 : 0 ≤ Q := div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (Nat.one_le_cast.mpr (hN k))))
        (Real.log_nonneg (Nat.one_le_cast.mpr (show 1 ≤ M k by have := hM k; omega)))
      change 2*((1+((1+Q)^s-1))^s⁻¹-1)=_
      rw [show 1+((1+Q)^s-1)=(1+Q)^s by ring,←Real.rpow_mul (add_nonneg zero_le_one h0),
        mul_inv_cancel₀ hs.ne',Real.rpow_one]
      dsimp [Q]; ring
    have hh := (hrecover.sub (tendsto_const_nhds (x:=(1:ℝ)))).const_mul 2
    simpa only [Pi.sub_apply,Pi.add_apply,add_zero,Real.one_rpow,sub_self,mul_zero,heq] using hh
  · intro h
    have hl := (fractional_modulation_loss_tendsto_zero_iff hs M N hM hN).mpr h
    exact squeeze_zero hn (fun k => (hb k).2) (by simpa only [zero_pow (by decide : (2:ℕ) ≠ 0)] using hl.pow 2)

#print axioms moebius_modulation_energy_sandwich
#print axioms uniform_squarefree_quantile_discrepancy
#print axioms relative_moebius_modulation_tendsto_zero_iff
#print axioms squarefree_modulation_quantile_finite_part
#print axioms centered_squarefree_modulation_quantile
#print axioms microscopic_squarefree_modulation_quantile

end GaloisForLFunctions.MultiscaleMollifiedZetaField.RandomDirichletJets
