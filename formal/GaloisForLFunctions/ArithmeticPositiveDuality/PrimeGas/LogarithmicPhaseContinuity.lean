import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.RefinementCharacters
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CompositionRigidity
import GaloisForLFunctions.HTGeometry.RealCharacterExp
import GaloisForLFunctions.SurfaceOfSpecZ.HasseWeilForPairsOfFrobeniusGraphs

/-!
# Selection of quantum time by continuity in energy

Logarithmic energy differences form a dense subgroup of the real line.
A multiplicative phase with uniformly close readings at nearby shell energies
extends to a continuous character of that line. The two prime energies at
2 and 3 distinguish its frequency.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open Set

/-- Uniformly close shell energies give uniformly close readings. -/
def energyContinuous {E : Type*} [PseudoMetricSpace E] (f : ℕ+ → E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ m n : ℕ+,
    dist (energy m) (energy n) < δ → dist (f m) (f n) < ε

/-- The multiplicative phase at a single real time. -/
def clockPhase (t : ℝ) : ℕ+ →* Circle where
  toFun n := Circle.exp (t * energy n)
  map_one' := by simp [energy]
  map_mul' a b := by rw [energy_mul, mul_add, Circle.exp_add]

private theorem dist_rotate (a b z : Circle) : dist (a*z) (b*z) = dist a b := by
  change dist ((a : ℂ)*(z : ℂ)) ((b : ℂ)*(z : ℂ)) = dist (a : ℂ) (b : ℂ)
  rw [dist_eq_norm, dist_eq_norm, ← sub_mul, norm_mul, Circle.norm_coe, mul_one]

private theorem dist_cross (a b c d : Circle) : dist (a/b) (c/d) = dist (a*d) (c*b) := by
  rw [← dist_rotate (a/b) (c/d) (b*d)]
  have left : a / b * (b*d) = a*d := by rw [← mul_assoc, div_mul_cancel]
  have right : c / d * (b*d) = c*b := by rw [mul_comm b d, ← mul_assoc, div_mul_cancel]
  rw [left, right]

/-- A common time gives a uniform energy resolution at every shell. -/
theorem clockPhase_energyContinuous (t : ℝ) : energyContinuous (clockPhase t) := by
  intro ε hε
  have hc : Continuous (fun x : ℝ => Circle.exp (t*x)) := Circle.exp.continuous.comp
    (continuous_const.mul continuous_id)
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := 0)) ε hε
  refine ⟨δ, hδ, fun m n hmn => ?_⟩
  have hd : dist (energy m-energy n) 0 < δ := by simpa only [Real.dist_eq, sub_zero] using hmn
  have hp := h hd
  simp only [mul_zero, Circle.exp_zero, mul_sub, Circle.exp_sub] at hp
  change dist (Circle.exp (t * energy m)) (Circle.exp (t * energy n)) < ε
  simpa only [div_mul_cancel, one_mul] using
    (dist_rotate (Circle.exp (t*energy m) / Circle.exp (t*energy n)) 1 (Circle.exp (t*energy n))).trans_lt hp

private def gap (p : ℕ+ × ℕ+) := energy p.1 - energy p.2
private abbrev Gaps := Set.range gap

private theorem dense_gaps : Dense Gaps := by
  apply SurfaceOfSpecZ.dense_logRatios.mono
  rintro x ⟨m,n,hm,hn,hx⟩
  exact ⟨(⟨m,hm⟩,⟨n,hn⟩), hx.symm⟩

private theorem energy_injective : Function.Injective energy := by
  intro a b h
  apply PNat.coe_injective
  have ha : (0 : ℝ) < (a : ℕ) := Nat.cast_pos.mpr a.pos
  have hb : (0 : ℝ) < (b : ℕ) := Nat.cast_pos.mpr b.pos
  have h' := congrArg Real.exp h
  simp only [energy, Real.exp_log ha, Real.exp_log hb] at h'
  exact_mod_cast h'

private def gapPhase (χ : ℕ+ →* Circle) (x : Gaps) : Circle :=
  χ x.property.choose.1 / χ x.property.choose.2

/-- Equality of two energy differences is exactly the cross-product identity on counts. -/
private theorem gapPhase_eq (χ : ℕ+ →* Circle) (x : Gaps) (a b : ℕ+) (h : gap (a,b) = x) :
    gapPhase χ x = χ a / χ b := by
  let p := x.property.choose
  have hp : gap p = x := x.property.choose_spec
  have he : energy p.1 - energy p.2 = energy a - energy b := hp.trans h.symm
  have hm : p.1*b = a*p.2 := energy_injective (by rw [energy_mul, energy_mul]; linarith)
  have hχ := congrArg χ hm
  simp only [map_mul] at hχ
  exact div_eq_div_iff_mul_eq_mul.mpr hχ

private theorem uniform_gapPhase (χ : ℕ+ →* Circle) (hc : energyContinuous χ) :
    UniformContinuous (gapPhase χ) := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hc ε hε
  refine ⟨δ, hδ, fun x y hxy => ?_⟩
  obtain ⟨⟨a,b⟩, hab⟩ := x.property
  obtain ⟨⟨c,d⟩, hcd⟩ := y.property
  rw [gapPhase_eq _ x a b hab, gapPhase_eq _ y c d hcd, dist_cross, ← map_mul, ← map_mul]
  apply h
  change dist (x : ℝ) (y : ℝ) < δ at hxy
  rw [← hab, ← hcd, Real.dist_eq] at hxy
  rw [energy_mul, energy_mul, Real.dist_eq]
  change |energy a - energy b - (energy c - energy d)| < δ at hxy
  rwa [show energy a + energy d - (energy c + energy b) =
    energy a - energy b - (energy c - energy d) by ring]

private theorem exists_clock (χ : ℕ+ →* Circle) (hc : energyContinuous χ) :
    ∃ t : ℝ, χ = clockPhase t := by
  let F := dense_gaps.extend (gapPhase χ)
  have hu := uniform_gapPhase χ hc
  have hF : Continuous F := (dense_gaps.uniformContinuous_extend hu).continuous
  have hpair (a b : ℕ+) : F (gap (a,b)) = χ a / χ b := by
    let x : Gaps := ⟨gap (a,b), (show gap (a,b) ∈ Gaps from ⟨(a,b),rfl⟩)⟩
    exact (dense_gaps.extend_of_ind hu x).trans (gapPhase_eq _ x _ _ rfl)
  have hAdd (x y : ℝ) : F (x+y) = F x * F y := by
    refine dense_gaps.denseRange_val.induction_on₂ (p := fun x y => F (x+y) = F x * F y) ?_ ?_ x y
    · exact isClosed_eq (hF.comp (continuous_fst.add continuous_snd))
        ((hF.comp continuous_fst).mul (hF.comp continuous_snd))
    · intro l r
      obtain ⟨⟨a,b⟩, ha⟩ := l.property
      obtain ⟨⟨c,d⟩, hb⟩ := r.property
      have hs : gap (a,b) + gap (c,d) = gap (a*c,b*d) := by
        simp only [gap, energy_mul]; ring
      rw [← ha, ← hb, hs, hpair, hpair, hpair, map_mul, map_mul, div_mul_div_comm]
  obtain ⟨t, ht⟩ := exists_exp_of_continuous_character (ψ := fun x => (F x : ℂ))
    (continuous_subtype_val.comp hF) (fun x y => by rw [hAdd, Circle.coe_mul]) (fun x => Circle.norm_coe _)
  refine ⟨t, MonoidHom.ext fun n => Circle.ext ?_⟩
  have hn : F (energy n) = χ n := by simpa [gap, energy, map_one] using hpair n 1
  exact (congrArg ((↑) : Circle → ℂ) hn.symm).trans (ht (energy n))

theorem clockPhase_injective : Function.Injective clockPhase := by
  intro t u h
  have he (r : ℝ) (n : ℕ+) : (clockPhase r n : ℂ) = heat (-(r : ℂ) * Complex.I) n := by
    change Complex.exp (((r*energy n : ℝ) : ℂ)*Complex.I) = _
    rw [heat, Complex.ofReal_mul]
    congr 1
    ring
  have eqHeat (n : ℕ+) : heat (-(t : ℂ)*Complex.I) n = heat (-(u : ℂ)*Complex.I) n := by
    rw [← he, ← he, h]
  have ht := two_prime_heat_injective (a₁ := -(t : ℂ)*Complex.I) (a₂ := -(u : ℂ)*Complex.I)
    (Prod.ext (eqHeat 2) (eqHeat 3))
  exact Complex.ofReal_injective (neg_injective (mul_right_cancel₀ Complex.I_ne_zero ht))

/-- A multiplicative circle phase comes from exactly one time if and only if nearby
energies have uniformly nearby phases. -/
theorem energyContinuous_iff_unique_time (χ : ℕ+ →* Circle) :
    energyContinuous χ ↔ ∃! t : ℝ, χ = clockPhase t := by
  constructor
  · intro hc
    obtain ⟨t, ht⟩ := exists_clock χ hc
    exact ⟨t, ht, fun u hu => clockPhase_injective (hu.symm.trans ht)⟩
  · rintro ⟨t, rfl, _⟩
    exact clockPhase_energyContinuous t

/-- Normalizing the singleton reading recovers its unit phase for a coherent measurement. -/
def measuredPhase (A : ℕ+ → ℕ+ → ℂ) (n : ℕ+) : ℂ := (Real.sqrt (n : ℕ) : ℂ) * A 1 n

private theorem read_phase {A : ℕ+ → ℕ+ → ℂ} {χ : ℕ+ →* Circle}
    (hf : ∀ m n, m ≤ n → A m n = refinementAmplitude χ m n) (n : ℕ+) :
    measuredPhase A n = (χ n : ℂ) := by
  have hv : singletonAmplitude χ 1 = 1 := by
    change (χ 1 : ℂ) / (Real.sqrt (1 : ℕ) : ℂ) = 1
    simp
  rw [measuredPhase, hf 1 n one_le, refinementAmplitude, hv, div_one]
  change (Real.sqrt (n : ℕ) : ℂ) * ((χ n : ℂ) / (Real.sqrt (n : ℕ) : ℂ)) = _
  have hn := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr n.pos : (0 : ℝ) < (n : ℕ))).ne'
  field_simp [hn]

/-- The spectral parameter associated to exp(itE) and a normalized singleton amplitude. -/
def timeParameter (t : ℝ) : ℂ := 1/2 - (t : ℂ)*Complex.I

theorem timeParameter_re (t : ℝ) : (timeParameter t).re = 1/2 := by
  norm_num [timeParameter, Complex.mul_re]

private theorem clock_singleton (t : ℝ) (n : ℕ+) :
    singletonAmplitude (clockPhase t) n = heat (timeParameter t) n := by
  have hpos : (0 : ℝ) < (n : ℕ) := Nat.cast_pos.mpr n.pos
  have hs : (Real.sqrt (n : ℕ) : ℂ) = Complex.exp ((energy n / 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_half, energy, Real.exp_log hpos]
  change Complex.exp (((t*energy n : ℝ) : ℂ)*Complex.I) / (Real.sqrt (n : ℕ) : ℂ) = _
  rw [hs, ← Complex.exp_sub, heat, timeParameter, Complex.ofReal_mul]
  push_cast
  congr 1
  ring

theorem clock_refinement_eq_heat (t : ℝ) (m n : ℕ+) :
    refinementAmplitude (clockPhase t) m n = heatRefinement (timeParameter t) m n := by
  rw [refinementAmplitude, heatRefinement, clock_singleton, clock_singleton]

/-- Coherent composition and continuity of observable singleton phases characterize
the entire critical-line heat family, without prescribing a power law for the amplitudes. -/
theorem measured_refinement_iff_unique_heat_time (A : ℕ+ → ℕ+ → ℂ) :
    coherentRefinement A ∧ energyContinuous (measuredPhase A) ↔
      ∃! t : ℝ, ∀ m n, m ≤ n → A m n = heatRefinement (timeParameter t) m n := by
  have read_at {t : ℝ} (ht : ∀ m n, m ≤ n → A m n = heatRefinement (timeParameter t) m n) :
      measuredPhase A = fun n => (clockPhase t n : ℂ) :=
    funext (read_phase (χ := clockPhase t) (fun m n h => (ht m n h).trans (clock_refinement_eq_heat t m n).symm))
  constructor
  · rintro ⟨hA, hc⟩
    obtain ⟨χ, hχ, _⟩ := (coherentRefinement_iff A).1 hA
    rw [funext (read_phase hχ)] at hc
    obtain ⟨t, ht, _⟩ := (energyContinuous_iff_unique_time χ).1 hc
    subst χ
    have htime (m n : ℕ+) (h : m ≤ n) := (hχ m n h).trans (clock_refinement_eq_heat t m n)
    refine ⟨t, htime, fun u hu => clockPhase_injective (MonoidHom.ext fun n => Circle.ext ?_)⟩
    exact congrFun ((read_at hu).symm.trans (read_at htime)) n
  · rintro ⟨t, ht, _⟩
    have hm := read_at ht
    refine ⟨(coherentRefinement_iff A).2 ⟨clockPhase t, ?_, ?_⟩, ?_⟩
    · intro m n h
      exact (ht m n h).trans (clock_refinement_eq_heat t m n).symm
    · intro ψ hψ
      exact MonoidHom.ext fun n => Circle.ext ((read_phase hψ n).symm.trans (congrFun hm n))
    · rw [hm]
      exact clockPhase_energyContinuous t

#print axioms clockPhase_energyContinuous
#print axioms clockPhase_injective
#print axioms energyContinuous_iff_unique_time
#print axioms clock_refinement_eq_heat
#print axioms measured_refinement_iff_unique_heat_time

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
