import GaloisForLFunctions.HTGeometry.SpinFourHiggsMechanism

/-!
# A geometric outer symmetry of the existing Spin(4) Higgs model

The missing-morphism mechanism in Gomes, arXiv:2607.24901v1, Proposition 3,
appears concretely on the corpus's two-sided quaternionic carrier: conjugation
exchanges the gauge factors and preserves the potential, but is not a gauge
transformation. Factor exchange is also outer on the product gauge group.
These are statements about the existing Spin(4) model; no identification with
all of SO(4), or classification of its full normalizer, is assumed.
-/

open scoped Quaternion
noncomputable section
set_option synthInstance.maxHeartbeats 100000
namespace GaloisForLFunctions.HTGeometry

/-- The factor exchange of the existing two-sided quaternionic gauge group. -/
def spinFourFactorSwap : SpinFourGaugeGroup ≃* SpinFourGaugeGroup := MulEquiv.prodComm

theorem spinFourFactorSwap_twice (g : SpinFourGaugeGroup) :
    spinFourFactorSwap (spinFourFactorSwap g) = g := rfl

/-- Quaternion conjugation realizes factor exchange on the Higgs carrier. -/
theorem quaternionStar_spinFour_intertwines (g : SpinFourGaugeGroup) (q : EventQuaternion) :
    star (g • q) = spinFourFactorSwap g • star q := by
  change star (g.1.1 * q * star g.2.1) = g.2.1 * star q * star g.1.1
  simp only [star_mul, star_star, mul_assoc]

/-- The geometric exchange preserves the full radial potential. -/
theorem spinFourHiggsPotential_star (q : EventQuaternion) :
    spinFourHiggsPotential (star q) = spinFourHiggsPotential q := by
  simp [spinFourHiggsPotential, quaternionHiggsPotential, Quaternion.normSq_star]

/-- The exchange fixes every element of the residual diagonal gauge group. -/
theorem spinFourFactorSwap_diagonal (u : QuaternionGaugeGroup) :
    spinFourFactorSwap (spinFourDiagonalResidual u) = spinFourDiagonalResidual u := rfl

/-- Exchanging the two factors is not conjugation by an element of their product. -/
theorem spinFourFactorSwap_outer :
    ¬ ∃ h : SpinFourGaugeGroup, ∀ g, spinFourFactorSwap g = h * g * h⁻¹ := by
  rintro ⟨h, hh⟩
  have hx := congrArg Prod.snd (hh (quaternionGaugeI, 1))
  have hi : quaternionGaugeI = 1 := by
    simpa [spinFourFactorSwap] using hx
  exact quaternionGaugeI_ne_one hi

/-- No gauge transformation on the existing Higgs carrier implements conjugation. -/
theorem quaternionStar_not_spinFour_gauge :
    ¬ ∃ g : SpinFourGaugeGroup, ∀ q : EventQuaternion, star q = g • q := by
  rintro ⟨g, hg⟩
  have hfix : g ∈ spinFourHiggsMechanism.unbroken := by
    rw [HiggsMechanism.unbroken, MulAction.mem_stabilizer_iff]
    change g • (1 : EventQuaternion) = 1
    simpa using (hg 1).symm
  have hdiag := (mem_spinFourHiggs_unbroken_iff_diagonal g).mp hfix
  have hinv : star g.1.1 * g.1.1 = (1 : EventQuaternion) := by
    rw [Quaternion.star_mul_self, quaternionGauge_normSq]
    rfl
  have ha (q : EventQuaternion) : star q = g.1.1 * q * star g.1.1 := by
    simpa only [show g • q = g.1.1 * q * star g.2.1 from rfl, hdiag] using hg q
  have hm (a b : EventQuaternion) : star (a * b) = star a * star b := by
    rw [ha (a*b), ha a, ha b]
    simp only [mul_assoc]
    rw [← mul_assoc (star g.1.1) g.1.1, hinv, one_mul]
  apply quaternionGaugeGroup_nonabelian
  intro u v
  apply Subtype.ext
  apply star_injective
  change star (u.1 * v.1) = star (v.1 * u.1)
  rw [hm, star_mul]

end GaloisForLFunctions.HTGeometry
