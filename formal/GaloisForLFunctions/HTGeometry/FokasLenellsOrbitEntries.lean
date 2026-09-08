import GaloisForLFunctions.HTGeometry.FokasLenellsRegularizedData

/-!
# Scalar off-diagonal equations in the Fokas–Lenells interaction frame

The constructed Volterra columns yield two scalar off-diagonal equations on
each oriented half-line. Free conjugation doubles the off-diagonal frequency
and cancels every diagonal phase. Their coordinates and spatial derivatives
have spectral-independent bounds from the existing effective-density
Gronwall estimate. These identities provide the input for integration by
parts and the regularized reflection-decay estimates of arXiv:2607.19649v1.
-/

open Complex Matrix Set MeasureTheory Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- Reflecting the spatial path changes the sign of every coefficient in its differential equation. -/
def orientedSchwartzEntry (f g h : SchwartzMap ℝ ℂ) (left : Bool) (i j : Fin 2) : SchwartzMap ℝ ℂ :=
  if left then -RHTower.negSchwartz' (effectiveSchwartzEntries f g h i j)
  else effectiveSchwartzEntries f g h i j

theorem orientedSchwartzEntry_apply (f g h : SchwartzMap ℝ ℂ) (left : Bool) (i j : Fin 2) (x : ℝ) :
    orientedSchwartzEntry f g h left i j x =
      if left then -effectiveSchwartzEntries f g h i j (-x) else effectiveSchwartzEntries f g h i j x := by
  cases left <;> simp [orientedSchwartzEntry, RHTower.negSchwartz'_apply]

theorem orientedEffectiveDensity_eq_entries (f g h : SchwartzMap ℝ ℂ) (left : Bool) (x : ℝ) :
    orientedEffectiveDensity f g h left x =
      ‖orientedSchwartzEntry f g h left 0 0 x‖+‖orientedSchwartzEntry f g h left 0 1 x‖+
      ‖orientedSchwartzEntry f g h left 1 0 x‖+‖orientedSchwartzEntry f g h left 1 1 x‖ := by
  cases left <;> simp [orientedEffectiveDensity, effectiveDensity, orientedSchwartzEntry_apply]

/-- The upper off-diagonal entry starts from the second basis vector, the lower from the first. -/
def offOrbitColumn (upper : Bool) : SpectralVector := if upper then (0,1) else (1,0)

def offOrbit (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) : ℂ :=
  if upper then (uniformizedOrbit f g h z (offOrbitColumn upper) left x).1
    else (uniformizedOrbit f g h z (offOrbitColumn upper) left x).2

def diagonalOrbit (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) : ℂ :=
  if upper then (uniformizedOrbit f g h z (offOrbitColumn upper) left x).2
    else (uniformizedOrbit f g h z (offOrbitColumn upper) left x).1

def offOrbitRate (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) : ℂ :=
  if upper then (uniformizedOrbitDerivative f g h z (offOrbitColumn upper) left x).1
    else (uniformizedOrbitDerivative f g h z (offOrbitColumn upper) left x).2

def diagonalOrbitRate (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) : ℂ :=
  if upper then (uniformizedOrbitDerivative f g h z (offOrbitColumn upper) left x).2
    else (uniformizedOrbitDerivative f g h z (offOrbitColumn upper) left x).1

def offOrbitDiagonal (f g h : SchwartzMap ℝ ℂ) (left upper : Bool) : SchwartzMap ℝ ℂ :=
  orientedSchwartzEntry f g h left (if upper then 0 else 1) (if upper then 0 else 1)

def offOrbitCoefficient (f g h : SchwartzMap ℝ ℂ) (left upper : Bool) : SchwartzMap ℝ ℂ :=
  orientedSchwartzEntry f g h left (if upper then 0 else 1) (if upper then 1 else 0)

def offOrbitFrequency (z : ℝ) (left upper : Bool) : ℝ :=
  if left then (if upper then -2*z else 2*z) else (if upper then 2*z else -2*z)

theorem offOrbitFrequency_abs (z : ℝ) (left upper : Bool) :
    |offOrbitFrequency z left upper| = 2*|z| := by
  cases left <;> cases upper <;> simp [offOrbitFrequency, abs_mul]

theorem offOrbitColumn_norm (upper : Bool) : ‖offOrbitColumn upper‖ = 1 := by
  cases upper <;> simp [offOrbitColumn, Prod.norm_def]

theorem offOrbit_initial (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) :
    offOrbit f g h z left upper 0 = 0 := by
  cases upper <;> simp [offOrbit, uniformizedOrbit_initial, offOrbitColumn]

theorem diagonalOrbit_initial (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) :
    diagonalOrbit f g h z left upper 0 = 1 := by
  cases upper <;> simp [diagonalOrbit, uniformizedOrbit_initial, offOrbitColumn]

theorem offOrbit_hasDerivAt (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) :
    HasDerivAt (offOrbit f g h z left upper) (offOrbitRate f g h z left upper x) x := by
  cases upper
  · exact (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x
      (uniformizedOrbit_hasDerivAt f g h z (offOrbitColumn false) left x)
  · exact (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x
      (uniformizedOrbit_hasDerivAt f g h z (offOrbitColumn true) left x)

theorem diagonalOrbit_hasDerivAt (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) :
    HasDerivAt (diagonalOrbit f g h z left upper) (diagonalOrbitRate f g h z left upper x) x := by
  cases upper
  · exact (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x
      (uniformizedOrbit_hasDerivAt f g h z (offOrbitColumn false) left x)
  · exact (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x
      (uniformizedOrbit_hasDerivAt f g h z (offOrbitColumn true) left x)

theorem offOrbit_continuous (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) :
    Continuous (offOrbit f g h z left upper) := by
  cases upper
  · exact (uniformizedOrbit_continuous f g h z _ left).snd
  · exact (uniformizedOrbit_continuous f g h z _ left).fst

theorem diagonalOrbit_continuous (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) :
    Continuous (diagonalOrbit f g h z left upper) := by
  cases upper
  · exact (uniformizedOrbit_continuous f g h z _ left).fst
  · exact (uniformizedOrbit_continuous f g h z _ left).snd

theorem offOrbitRate_continuous (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) :
    Continuous (offOrbitRate f g h z left upper) := by
  cases upper
  · exact (uniformizedOrbitDerivative_continuous f g h z _ left).snd
  · exact (uniformizedOrbitDerivative_continuous f g h z _ left).fst

theorem diagonalOrbitRate_continuous (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) :
    Continuous (diagonalOrbitRate f g h z left upper) := by
  cases upper
  · exact (uniformizedOrbitDerivative_continuous f g h z _ left).fst
  · exact (uniformizedOrbitDerivative_continuous f g h z _ left).snd

theorem staggerPhase_mul_opposite (z x : ℝ) :
    FDNLS.staggerPhase z x*FDNLS.staggerPhase (-z) x = 1 := by
  simp [FDNLS.staggerPhase, ← Complex.exp_add]

theorem staggerPhase_square (z x : ℝ) :
    FDNLS.staggerPhase z x*FDNLS.staggerPhase z x = FDNLS.staggerPhase (2*z) x := by
  unfold FDNLS.staggerPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem staggerPhase_neg_time (z x : ℝ) : FDNLS.staggerPhase z (-x) = FDNLS.staggerPhase (-z) x := by
  unfold FDNLS.staggerPhase
  congr 1
  push_cast
  ring

/-- Free conjugation cancels diagonal phases and doubles the off-diagonal frequency. -/
theorem rotatingFrame_pairOperator (a b c d : ℂ) (z x : ℝ) (v : SpectralVector) :
    rotatingFrame z x (pairOperator a b c d (rotatingFrame (-z) x v)) =
      (a*v.1+FDNLS.staggerPhase (2*z) x*(b*v.2),
       FDNLS.staggerPhase (-2*z) x*(c*v.1)+d*v.2) := by
  have hp := staggerPhase_mul_opposite z x
  have hn : FDNLS.staggerPhase (-z) x*FDNLS.staggerPhase z x = 1 := by simpa [mul_comm] using hp
  have hs := staggerPhase_square z x
  have ht : FDNLS.staggerPhase (-z) x*FDNLS.staggerPhase (-z) x = FDNLS.staggerPhase (-2*z) x := by
    simpa only [mul_neg, neg_mul] using staggerPhase_square (-z) x
  apply Prod.ext
  · change FDNLS.staggerPhase z x*(a*(FDNLS.staggerPhase (-z) x*v.1)+
        b*(FDNLS.staggerPhase (-(-z)) x*v.2)) = _
    rw [neg_neg]
    calc
      _ = (FDNLS.staggerPhase z x*FDNLS.staggerPhase (-z) x)*(a*v.1)+
        (FDNLS.staggerPhase z x*FDNLS.staggerPhase z x)*(b*v.2) := by ring
      _ = _ := by rw [hp,hs,one_mul]
  · change FDNLS.staggerPhase (-z) x*(c*(FDNLS.staggerPhase (-z) x*v.1)+
        d*(FDNLS.staggerPhase (-(-z)) x*v.2)) = _
    rw [neg_neg]
    calc
      _ = (FDNLS.staggerPhase (-z) x*FDNLS.staggerPhase (-z) x)*(c*v.1)+
        (FDNLS.staggerPhase (-z) x*FDNLS.staggerPhase z x)*(d*v.2) := by ring
      _ = _ := by rw [ht,hn,one_mul]

/-- The scalar equation splits into diagonal transport and an oscillatory source. -/
theorem offOrbitRate_eq (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) :
    offOrbitRate f g h z left upper x =
      offOrbitDiagonal f g h left upper x*offOrbit f g h z left upper x+
      FDNLS.staggerPhase (offOrbitFrequency z left upper) x*
        (offOrbitCoefficient f g h left upper x*diagonalOrbit f g h z left upper x) := by
  cases left <;> cases upper <;>
    simp [offOrbitRate, offOrbitDiagonal, offOrbit, diagonalOrbit, offOrbitCoefficient,
      orientedSchwartzEntry_apply, uniformizedOrbitDerivative, uniformizedOrbit,
      uniformizedInteractionRate, effectiveOperator, rotatingFrame_pairOperator, offOrbitFrequency,
      staggerPhase_neg_time, neg_mul] <;> ring

/-- Every coordinate is bounded independently of real spectrum and distance along either half-line. -/
theorem offOrbit_coordinates_bound (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) :
    ‖offOrbit f g h z left upper |x|‖ ≤ Real.exp (effectiveMass f g h) ∧
    ‖diagonalOrbit f g h z left upper |x|‖ ≤ Real.exp (effectiveMass f g h) := by
  have hb := uniformizedOrbit_bound f g h z (offOrbitColumn upper) left x
  rw [offOrbitColumn_norm, one_mul] at hb
  cases upper
  · exact ⟨(norm_snd_le _).trans hb,(norm_fst_le _).trans hb⟩
  · exact ⟨(norm_fst_le _).trans hb,(norm_snd_le _).trans hb⟩

theorem diagonalOrbitRate_bound (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (left upper : Bool) (x : ℝ) :
    ‖diagonalOrbitRate f g h z left upper |x|‖ ≤
      orientedEffectiveDensity f g h left |x| * Real.exp (effectiveMass f g h) := by
  have hb := uniformizedOrbitDerivative_bound f g h z (offOrbitColumn upper) left |x|
  have hu := uniformizedOrbit_bound f g h z (offOrbitColumn upper) left x
  rw [offOrbitColumn_norm, one_mul] at hu
  have hd := hb.trans (mul_le_mul_of_nonneg_left hu (orientedEffectiveDensity_nonneg f g h left |x|))
  cases upper
  · exact (norm_fst_le _).trans hd
  · exact (norm_snd_le _).trans hd

/-- A diagonal coefficient is dominated by the already integrable effective density. -/
theorem offOrbitDiagonal_le_density (f g h : SchwartzMap ℝ ℂ) (left upper : Bool) (x : ℝ) :
    ‖offOrbitDiagonal f g h left upper x‖ ≤ orientedEffectiveDensity f g h left x := by
  rw [orientedEffectiveDensity_eq_entries]
  cases upper <;> simp only [offOrbitDiagonal, Bool.false_eq_true, ↓reduceIte] <;>
    linarith [norm_nonneg (orientedSchwartzEntry f g h left 0 0 x),
      norm_nonneg (orientedSchwartzEntry f g h left 0 1 x),
      norm_nonneg (orientedSchwartzEntry f g h left 1 0 x),
      norm_nonneg (orientedSchwartzEntry f g h left 1 1 x)]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
