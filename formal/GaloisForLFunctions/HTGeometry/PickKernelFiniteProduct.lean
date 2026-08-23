import GaloisForLFunctions.HTGeometry.PickKernelProduct

/-!
# Ordered finite-product expansion for Pick kernels

An ordered product of scalar factors has a Pick kernel that telescopes into
one term per factor.  The companion data pair records simultaneously the
prefix product at the left node and the accumulated kernel expansion.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

/-- Left-node product and Pick-kernel expansion accumulated over an ordered factor list. -/
def pickKernelProductData (fs : List (ℂ → ℂ)) (z w : ℂ) : ℂ × ℂ :=
  fs.foldr (fun f acc =>
    (f z * acc.1,
      acc.1 * pickKernel f z w + starRingEnd ℂ (f w) * acc.2)) (1, 0)

theorem pickKernelProductData_fst
    (fs : List (ℂ → ℂ)) (z w : ℂ) :
    (pickKernelProductData fs z w).1 = (fs.map fun f => f z).prod := by
  induction fs with
  | nil => simp [pickKernelProductData]
  | cons f fs ih =>
      change f z * (pickKernelProductData fs z w).1 =
        f z * (fs.map fun g => g z).prod
      rw [ih]

/-- Exact telescoping expansion of the Pick kernel of every finite ordered product. -/
theorem pickKernel_productList
    (fs : List (ℂ → ℂ)) (z w : ℂ) :
    pickKernel (fun ζ => (fs.map fun f => f ζ).prod) z w =
      (pickKernelProductData fs z w).2 := by
  induction fs with
  | nil => simp [pickKernelProductData, pickKernel]
  | cons f fs ih =>
      change pickKernel (fun ζ => f ζ * (fs.map fun g => g ζ).prod) z w =
        (pickKernelProductData (f :: fs) z w).2
      rw [pickKernel_mul, ih, ← pickKernelProductData_fst fs z w]
      rfl

end

end GaloisForLFunctions.HTGeometry
