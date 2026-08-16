import GaloisForLFunctions.HTGeometry.SteinbergTorusCommutator

/-!
# The torus is a homomorphism modulo `K₂`

The torus elements fail to be multiplicative exactly by the Steinberg symbol, and fail to commute
exactly by the asymmetry of that symbol.  Both failures live in `K₂`, so in the quotient
`St(R)/K₂` the map

```text
u ⟼ ⟦h_ij(u)⟧
```

is a genuine group homomorphism from the units of `R`, landing in a subgroup where the images
commute.

This is the starting point of Matsumoto's presentation: the symbol `{u,v}` measures the failure of
a section of `St(R) → St(R)/K₂` over the torus to be multiplicative, and the whole theory of `K₂` of
a field is the computation of that obstruction.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- The images of the torus elements commute in the quotient. -/
theorem commute_mk_steinbergTorus {i j : n} (hij : i ≠ j) (u v : Rˣ) :
    Commute (QuotientGroup.mk (s := KTwo R n) (steinbergTorus hij u))
      (QuotientGroup.mk (s := KTwo R n) (steinbergTorus hij v)) := by
  have hmem := torus_commutator_mem_KTwo hij u v
  have h1 : (QuotientGroup.mk (s := KTwo R n)
      (steinbergTorus hij u * steinbergTorus hij v * (steinbergTorus hij u)⁻¹
        * (steinbergTorus hij v)⁻¹)) = 1 :=
    (QuotientGroup.eq_one_iff _).2 hmem
  have h2 : (QuotientGroup.mk (s := KTwo R n) (steinbergTorus hij u))
      * (QuotientGroup.mk (s := KTwo R n) (steinbergTorus hij v))
      * (QuotientGroup.mk (s := KTwo R n) (steinbergTorus hij u))⁻¹
      * (QuotientGroup.mk (s := KTwo R n) (steinbergTorus hij v))⁻¹ = 1 := by
    simpa using h1
  show (QuotientGroup.mk (s := KTwo R n) (steinbergTorus hij u))
      * (QuotientGroup.mk (s := KTwo R n) (steinbergTorus hij v))
      = (QuotientGroup.mk (s := KTwo R n) (steinbergTorus hij v))
        * (QuotientGroup.mk (s := KTwo R n) (steinbergTorus hij u))
  calc (QuotientGroup.mk (s := KTwo R n) (steinbergTorus hij u))
        * (QuotientGroup.mk (s := KTwo R n) (steinbergTorus hij v))
      = ((QuotientGroup.mk (s := KTwo R n) (steinbergTorus hij u))
          * (QuotientGroup.mk (s := KTwo R n) (steinbergTorus hij v))
          * (QuotientGroup.mk (s := KTwo R n) (steinbergTorus hij u))⁻¹
          * (QuotientGroup.mk (s := KTwo R n) (steinbergTorus hij v))⁻¹)
        * ((QuotientGroup.mk (s := KTwo R n) (steinbergTorus hij v))
          * (QuotientGroup.mk (s := KTwo R n) (steinbergTorus hij u))) := by group
    _ = (QuotientGroup.mk (s := KTwo R n) (steinbergTorus hij v))
          * (QuotientGroup.mk (s := KTwo R n) (steinbergTorus hij u)) := by
        rw [h2, one_mul]

/-- **The torus descends to a group homomorphism on the quotient by `K₂`.** -/
def steinbergTorusQuotientHom {i j : n} (hij : i ≠ j) :
    Rˣ →* (SteinbergGroup R n ⧸ KTwo R n) where
  toFun u := QuotientGroup.mk (steinbergTorus hij u)
  map_one' := by
    show QuotientGroup.mk (s := KTwo R n) (steinbergTorus hij 1) = 1
    rw [steinbergTorus_one]
    rfl
  map_mul' u v := by
    show QuotientGroup.mk (s := KTwo R n) (steinbergTorus hij (u * v))
      = QuotientGroup.mk (s := KTwo R n) (steinbergTorus hij u)
        * QuotientGroup.mk (s := KTwo R n) (steinbergTorus hij v)
    have hS : (QuotientGroup.mk (s := KTwo R n) (steinbergSymbol hij u v)) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (steinbergSymbol_mem_KTwo hij u v)
    rw [steinbergTorus_mul hij u v]
    have hmk : QuotientGroup.mk (s := KTwo R n)
        (steinbergSymbol hij u v * steinbergTorus hij v * steinbergTorus hij u)
        = QuotientGroup.mk (s := KTwo R n) (steinbergSymbol hij u v)
          * QuotientGroup.mk (s := KTwo R n) (steinbergTorus hij v)
          * QuotientGroup.mk (s := KTwo R n) (steinbergTorus hij u) := by
      simp only [QuotientGroup.mk_mul]
    rw [hmk, hS, one_mul]
    exact (commute_mk_steinbergTorus hij u v).symm.eq

@[simp]
theorem steinbergTorusQuotientHom_apply {i j : n} (hij : i ≠ j) (u : Rˣ) :
    steinbergTorusQuotientHom hij u = QuotientGroup.mk (steinbergTorus hij u) := rfl

omit [DecidableEq n] [Fintype n] in
/-- **The symbol is exactly the multiplicativity defect of the torus.**  In the quotient it
vanishes, which is the content of the homomorphism above. -/
theorem steinbergSymbol_eq_torus_defect {i j : n} (hij : i ≠ j) (u v : Rˣ) :
    steinbergSymbol hij u v
      = steinbergTorus hij (u * v) * (steinbergTorus hij v * steinbergTorus hij u)⁻¹ := by
  rw [steinbergTorus_mul hij u v]
  group

end GaloisForLFunctions.HTGeometry

end
