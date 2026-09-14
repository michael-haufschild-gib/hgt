import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Similarity-coordinate derivative operators

This file formalizes Lemma 4.1 and equation (4.2) of the supplied Navier--Stokes
paper.  Differentiating the two defining similarity relations gives a `2 × 2`
linear system.  Its determinant is `L = 1 - 2hη²`; solving it produces the
time and axial coordinate rates.  A Fréchet chain rule then gives the paper's
operators `T_b` and `Z_b` on every weighted profile `q^b f(X,η)`.

The coordinate solve and profile chain rule are separated so either layer can be
reused independently.
-/

namespace GaloisForLFunctions.HTGeometry.NavierStokesSimilarityDerivatives

noncomputable section

/-- Similarity exponent `D = 1/2 - h`. -/
def similarityD (h : ℝ) : ℝ := 1 / 2 - h

/-- Disk factor `d = 1 - η²`. -/
def similarityDisk (eta : ℝ) : ℝ := 1 - eta ^ 2

/-- Coordinate determinant `L = 1 - 2hη²`. -/
def similarityGap (h eta : ℝ) : ℝ := 1 - 2 * h * eta ^ 2

theorem similarityGap_eq_disk_add (h eta : ℝ) :
    similarityGap h eta = similarityDisk eta + 2 * similarityD h * eta ^ 2 := by
  simp [similarityGap, similarityDisk, similarityD]
  ring

/-- Solving the differentiated fixed-axial-position system gives the time rates in Lemma 4.1. -/
theorem timeCoordinateRates_of_linearSystem
    {h q eta qdot etadot : ℝ} (hqpos : 0 < q) (hgap : similarityGap h eta ≠ 0)
    (htime : qdot * similarityDisk eta - 2 * q * eta * etadot = -1)
    (hfixedAxial :
      similarityD h * q ^ (similarityD h - 1) * qdot * eta +
        q ^ similarityD h * etadot = 0) :
    qdot = -1 / similarityGap h eta ∧
      etadot = similarityD h * eta / (q * similarityGap h eta) := by
  have hqne : q ≠ 0 := hqpos.ne'
  have hqDne : q ^ similarityD h ≠ 0 := (Real.rpow_pos_of_pos hqpos _).ne'
  have hfactor :
      q ^ similarityD h *
          (similarityD h * qdot * eta / q + etadot) = 0 := by
    rw [Real.rpow_sub_one hqne] at hfixedAxial
    rw [← hfixedAxial]
    field_simp [hqne]
  have hinner : similarityD h * qdot * eta / q + etadot = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hqDne
  have heta : etadot = -(similarityD h * qdot * eta / q) := by
    linarith
  have hqdotGap : qdot * similarityGap h eta = -1 := by
    calc
      qdot * similarityGap h eta =
          qdot * (similarityDisk eta + 2 * similarityD h * eta ^ 2) := by
            rw [similarityGap_eq_disk_add]
      _ = qdot * similarityDisk eta - 2 * q * eta * etadot := by
        rw [heta]
        field_simp [hqne]
        ring
      _ = -1 := htime
  constructor
  · exact (eq_div_iff hgap).2 hqdotGap
  · rw [heta, (eq_div_iff hgap).2 hqdotGap]
    field_simp [hqne, hgap]

/-- Solving the differentiated fixed-time system gives the axial rates in Lemma 4.1. -/
theorem axialCoordinateRates_of_linearSystem
    {h q eta qdot etadot : ℝ} (hqpos : 0 < q) (hgap : similarityGap h eta ≠ 0)
    (hfixedTime : qdot * similarityDisk eta - 2 * q * eta * etadot = 0)
    (haxial :
      similarityD h * q ^ (similarityD h - 1) * qdot * eta +
        q ^ similarityD h * etadot = 1) :
    qdot = 2 * eta * q ^ (1 - similarityD h) / similarityGap h eta ∧
      etadot = similarityDisk eta /
        (q ^ similarityD h * similarityGap h eta) := by
  have hqne : q ≠ 0 := hqpos.ne'
  have hqDne : q ^ similarityD h ≠ 0 := (Real.rpow_pos_of_pos hqpos _).ne'
  have hnormalized :
      similarityD h * qdot * eta / q + etadot =
        1 / q ^ similarityD h := by
    rw [Real.rpow_sub_one hqne] at haxial
    apply (eq_div_iff hqDne).2
    rw [← haxial]
    field_simp [hqne]
  have hetaGap :
      etadot * similarityGap h eta =
        similarityDisk eta / q ^ similarityD h := by
    calc
      etadot * similarityGap h eta =
          etadot * (similarityDisk eta + 2 * similarityD h * eta ^ 2) := by
            rw [similarityGap_eq_disk_add]
      _ = similarityDisk eta *
          (similarityD h * qdot * eta / q + etadot) := by
        have htransport : qdot * similarityDisk eta = 2 * q * eta * etadot := by
          linarith [hfixedTime]
        calc
          etadot * (similarityDisk eta + 2 * similarityD h * eta ^ 2) =
              similarityDisk eta * etadot +
                similarityD h * eta / q *
                  (2 * q * eta * etadot) := by
                    field_simp [hqne]
          _ = similarityDisk eta * etadot +
                similarityD h * eta / q *
                  (qdot * similarityDisk eta) := by rw [htransport]
          _ = similarityDisk eta *
                (similarityD h * qdot * eta / q + etadot) := by ring
      _ = similarityDisk eta / q ^ similarityD h := by
        rw [hnormalized]
        simp [div_eq_mul_inv]
  have hqdotGap :
      qdot * similarityGap h eta =
        2 * eta * q ^ (1 - similarityD h) := by
    calc
      qdot * similarityGap h eta =
          qdot * (similarityDisk eta + 2 * similarityD h * eta ^ 2) := by
            rw [similarityGap_eq_disk_add]
      _ = 2 * q * eta *
          (similarityD h * qdot * eta / q + etadot) := by
        field_simp [hqne]
        nlinarith [hfixedTime]
      _ = 2 * q * eta / q ^ similarityD h := by
        rw [hnormalized]
        simp [div_eq_mul_inv]
      _ = 2 * eta * q ^ (1 - similarityD h) := by
        rw [Real.rpow_sub hqpos]
        rw [Real.rpow_one]
        ring
  constructor
  · exact (eq_div_iff hgap).2 hqdotGap
  · apply (eq_div_iff (mul_ne_zero hqDne hgap)).2
    calc
      etadot * (q ^ similarityD h * similarityGap h eta) =
          q ^ similarityD h *
            (etadot * similarityGap h eta) := by ring
      _ = q ^ similarityD h *
          (similarityDisk eta / q ^ similarityD h) := by rw [hetaGap]
      _ = similarityDisk eta := by field_simp [hqDne]

/-- Differential of a scalar profile in `(X, η)` coordinates. -/
def profileDifferential (fX fη : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  fX • ContinuousLinearMap.fst ℝ ℝ ℝ +
    fη • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp]
theorem profileDifferential_apply (fX fη dX dη : ℝ) :
    profileDifferential fX fη (dX, dη) = fX * dX + fη * dη := by
  simp [profileDifferential]

/-- Chain rule for a profile evaluated along moving similarity coordinates. -/
theorem profileAlong_hasDerivAt {f : ℝ × ℝ → ℝ} {X η : ℝ → ℝ}
    {fX fη Xdot ηdot t : ℝ}
    (hf : HasFDerivAt f (profileDifferential fX fη) (X t, η t))
    (hX : HasDerivAt X Xdot t) (hη : HasDerivAt η ηdot t) :
    HasDerivAt (fun s ↦ f (X s, η s)) (fX * Xdot + fη * ηdot) t := by
  simpa only [Function.comp_def, profileDifferential_apply] using
    hf.comp_hasDerivAt t (hX.prodMk hη)

/-- Profile multiplied by its similarity weight `q^b`. -/
def scaledProfile (q X η : ℝ → ℝ) (b : ℝ) (f : ℝ × ℝ → ℝ) (t : ℝ) : ℝ :=
  q t ^ b * f (X t, η t)

/-- Time operator `T_b` from equation (4.2), with `DXf = X ∂_X f`. -/
def timeSimilarityOperator (D L b η f fη DXf : ℝ) : ℝ :=
  L⁻¹ * (-b * f + D * η * fη + DXf)

/-- Axial operator `Z_b` from equation (4.2). -/
def axialSimilarityOperator (d L b η f fη DXf : ℝ) : ℝ :=
  L⁻¹ * (2 * b * η * f + d * fη - 2 * η * DXf)

/-- Time-derivative half of Lemma 4.1. -/
theorem scaledProfile_time_hasDerivAt
    {q X η : ℝ → ℝ} {f : ℝ × ℝ → ℝ}
    {D L b fX fη t : ℝ}
    (hqpos : 0 < q t) (hL : L ≠ 0)
    (hq : HasDerivAt q (-1 / L) t)
    (hX : HasDerivAt X (X t / (q t * L)) t)
    (hη : HasDerivAt η (D * η t / (q t * L)) t)
    (hf : HasFDerivAt f (profileDifferential fX fη) (X t, η t)) :
    HasDerivAt (scaledProfile q X η b f)
      (q t ^ (b - 1) *
        timeSimilarityOperator D L b (η t) (f (X t, η t)) fη (X t * fX)) t := by
  have hpow := hq.rpow_const (p := b) (Or.inl hqpos.ne')
  have hprofile := profileAlong_hasDerivAt hf hX hη
  have hproduct := hpow.mul hprofile
  apply hproduct.congr_deriv
  rw [Real.rpow_sub_one hqpos.ne']
  simp only [timeSimilarityOperator]
  field_simp [hqpos.ne', hL]
  ring

/-- Axial-derivative half of Lemma 4.1. -/
theorem scaledProfile_axial_hasDerivAt
    {q X η : ℝ → ℝ} {f : ℝ × ℝ → ℝ}
    {D d L b fX fη z : ℝ}
    (hqpos : 0 < q z) (hL : L ≠ 0)
    (hq : HasDerivAt q (2 * η z * q z ^ (1 - D) / L) z)
    (hX : HasDerivAt X (-2 * η z * X z / (q z ^ D * L)) z)
    (hη : HasDerivAt η (d / (q z ^ D * L)) z)
    (hf : HasFDerivAt f (profileDifferential fX fη) (X z, η z)) :
    HasDerivAt (scaledProfile q X η b f)
      (q z ^ (b - D) *
        axialSimilarityOperator d L b (η z) (f (X z, η z)) fη (X z * fX)) z := by
  have hpow := hq.rpow_const (p := b) (Or.inl hqpos.ne')
  have hprofile := profileAlong_hasDerivAt hf hX hη
  have hproduct := hpow.mul hprofile
  apply hproduct.congr_deriv
  rw [Real.rpow_sub_one hqpos.ne', Real.rpow_sub hqpos b D,
    Real.rpow_sub hqpos 1 D]
  have hqD : q z ^ D ≠ 0 := (Real.rpow_pos_of_pos hqpos D).ne'
  simp only [axialSimilarityOperator, Real.rpow_one]
  field_simp [hqpos.ne', hqD, hL]
  ring

end

end GaloisForLFunctions.HTGeometry.NavierStokesSimilarityDerivatives
