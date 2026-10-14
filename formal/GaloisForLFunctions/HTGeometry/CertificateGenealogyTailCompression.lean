import GaloisForLFunctions.HTGeometry.NormalizedGenealogyTail
import GaloisForLFunctions.HTGeometry.ScalarCertificateGramCompletion
import GaloisForLFunctions.HTGeometry.PaperGenealogyGramCompletion

/-! # Literal infinite tails of the native certificate genealogies

Deleting an initial segment is the actual backward/forward compression of the
original full genealogy. The original certificate bounds and invertibility are
preserved; no new operator or analytic assumptions are supplied by the caller.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open _root_.ContinuousLinearMap Filter Topology

def scalarCertificateTail (a : CertStream) (k : ℕ) : CertStream where
  c n := a.c (n + k)
  pos n := a.pos (n + k)
  bound := a.bound
  le_bound n := a.le_bound (n + k)

@[simp] theorem scalarCertificateTail_zero (a : CertStream) : scalarCertificateTail a 0 = a := rfl

@[simp] theorem scalarCertificateTail_coefficient (a : CertStream) (k n : ℕ) :
    (scalarCertificateTail a k).c n = a.c (n + k) := rfl

def paperCertificateTail {d : ℕ} (a : OpCertStream d) (k : ℕ) : OpCertStream d where
  C n := a.C (n + k)
  unit n := a.unit (n + k)
  bound := a.bound
  bound_nonneg := a.bound_nonneg
  le_bound n := a.le_bound (n + k)

@[simp] theorem paperCertificateTail_zero {d : ℕ} (a : OpCertStream d) :
    paperCertificateTail a 0 = a := rfl

@[simp] theorem paperCertificateTail_coefficient (a : OpCertStream 1) (k n : ℕ) :
    scalarCertificateCoefficient (paperCertificateTail a k) n = scalarCertificateCoefficient a (n + k) := rfl

theorem scalarGenealogy_tail_compression_apply {G : ToeplitzSpace →L[ℂ] ToeplitzSpace}
    {w : ℕ → ℂ} (hG : ∀ (f : ToeplitzSpace) (n : ℕ), G f n = f n - w n * f (n + 1))
    (k : ℕ) (f : ToeplitzSpace) (n : ℕ) :
    ((backOp k ∘L G) ∘L shiftOp k) f n = f n - w (n + k) * f (n + 1) := by
  change G (shiftOp k f) (n + k) = _
  rw [hG, shiftOp_apply, shiftFun_add, shiftOp_apply,
    show n + k + 1 = (n + 1) + k by omega, shiftFun_add]

theorem scalarCertificateTail_genealogy (a : CertStream) (k : ℕ) :
    (scalarCertificateTail a k).genealogy = (backOp k ∘L a.genealogy) ∘L shiftOp k := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext n
  rw [CertStream.genealogy_apply, scalarGenealogy_tail_compression_apply a.genealogy_apply]
  rfl

theorem scalarCoordinateGenealogy_tail (a : OpCertStream 1) (k : ℕ) :
    scalarCoordinateGenealogy (paperCertificateTail a k) =
      (backOp k ∘L scalarCoordinateGenealogy a) ∘L shiftOp k := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext n
  rw [scalarCoordinateGenealogy_apply,
    scalarGenealogy_tail_compression_apply (scalarCoordinateGenealogy_apply a)]
  rfl

def paperGenealogyTailBack (k : ℕ) : FibSeq 1 →L[ℂ] FibSeq 1 :=
  RHTower.unitaryPush scalarCertificateCoordinates.symm (backOp k)

def paperGenealogyTailShift (k : ℕ) : FibSeq 1 →L[ℂ] FibSeq 1 :=
  RHTower.unitaryPush scalarCertificateCoordinates.symm (shiftOp k)

theorem paperCertificateTail_genealogy (a : OpCertStream 1) (k : ℕ) :
    (paperCertificateTail a k).genealogy =
      (paperGenealogyTailBack k ∘L a.genealogy) ∘L paperGenealogyTailShift k := by
  rw [paperGenealogy_eq_unitaryPush_scalarCoordinates (paperCertificateTail a k),
    scalarCoordinateGenealogy_tail]
  change RHTower.unitaryPush scalarCertificateCoordinates.symm
    (backOp k * scalarCoordinateGenealogy a * shiftOp k) = _
  rw [RHTower.unitaryPush_mul, RHTower.unitaryPush_mul,
    ← paperGenealogy_eq_unitaryPush_scalarCoordinates a]
  rfl

theorem scalarGenealogyGramCompletion_eq_tailValue
    {G : ToeplitzSpace →L[ℂ] ToeplitzSpace} {w : ℕ → ℂ}
    (hG : ∀ j, G (lpBasisVec j) = finiteGenealogyColumn w j)
    (hs : Summable (fun n => ‖w n‖ ^ 2)) :
    scalarGenealogyGramCompletion G w = (normalizedGenealogyTailValue w 0 : ℂ) := by
  have hc := ((scalarGenealogyGramCompletion_spec_iff hG).mpr hs).2.2
  have hr := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_normalizedGenealogyTailValue w hs 0)
  exact tendsto_nhds_unique hc hr

theorem scalarCertificateTailGram_eq (a : CertStream)
    (hs : Summable (fun n => a.c n ^ 2)) (k : ℕ) :
    scalarCertificateGramCompletion (scalarCertificateTail a k) =
      (normalizedGenealogyTailValue (fun n => (a.c n : ℂ)) k : ℂ) := by
  have ht : Summable (fun n => ‖((scalarCertificateTail a k).c n : ℂ)‖ ^ 2) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (a.pos _),
      scalarCertificateTail_coefficient] using (summable_nat_add_iff k).mpr hs
  have he := scalarGenealogyGramCompletion_eq_tailValue
    (scalarCertificate_genealogy_basis (scalarCertificateTail a k)) ht
  exact he

theorem paperCertificateTailGram_eq (a : OpCertStream 1)
    (hs : Summable (fun n => ‖scalarCertificateCoefficient a n‖ ^ 2)) (k : ℕ) :
    paperGenealogyGramCompletion (paperCertificateTail a k) =
      (normalizedGenealogyTailValue (scalarCertificateCoefficient a) k : ℂ) := by
  rw [paperGenealogyGramCompletion_eq_scalar]
  have ht : Summable (fun n => ‖scalarCertificateCoefficient (paperCertificateTail a k) n‖ ^ 2) :=
    (summable_nat_add_iff k).mpr hs
  have he := scalarGenealogyGramCompletion_eq_tailValue
    (scalarCoordinateGenealogy_basis (paperCertificateTail a k)) ht
  exact he

end
end GaloisForLFunctions.HTGeometry
