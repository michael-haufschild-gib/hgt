import GaloisForLFunctions.HTGeometry.PolynomialODE.OddCompactHeadExpansion

/-!
# Drift grades of the reflected source scalars

The drift grade of degree `d` is the part of the scalar homogeneous of degree
`d` in `u`. Each scalar is the sum of its grades.
-/

namespace HTGeometry
noncomputable section
set_option maxRecDepth 4000

/-- Drift degree 0 of the reflected source scalar 2. -/
def oddCompactReflectedScalar2Grade0 (_u a w : ℝ) : ℝ :=
  ((-720 : ℝ) +
    (660 : ℝ)*a^(1 : ℕ) +
    (-84 : ℝ)*a^(2 : ℕ) +
    (-192 : ℝ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-1 : ℝ)*a^(3 : ℕ)) / (1024 : ℝ)

/-- Drift degree 1 of the reflected source scalar 2. -/
def oddCompactReflectedScalar2Grade1 (u a w : ℝ) : ℝ :=
  ((6 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (1 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ)) / (192 : ℝ)

/-- Drift degree 2 of the reflected source scalar 2. -/
def oddCompactReflectedScalar2Grade2 (u a w : ℝ) : ℝ :=
  ((540 : ℝ)*u^(2 : ℕ) +
    (-210 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ) +
    (-1 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ) +
    (48 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ)) / (2304 : ℝ)

/-- Drift degree 3 of the reflected source scalar 2. -/
def oddCompactReflectedScalar2Grade3 (u a w : ℝ) : ℝ :=
  ((-1 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ)) / (288 : ℝ)

/-- Drift degree 4 of the reflected source scalar 2. -/
def oddCompactReflectedScalar2Grade4 (u a _w : ℝ) : ℝ :=
  ((-60 : ℝ)*u^(4 : ℕ) +
    (5 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)) / (2304 : ℝ)

/-- Drift degree 6 of the reflected source scalar 2. -/
def oddCompactReflectedScalar2Grade6 (u _a _w : ℝ) : ℝ :=
  ((5 : ℝ)*u^(6 : ℕ)) / (5184 : ℝ)

/-- The reflected source scalar 2 is the sum of its drift grades. -/
theorem oddCompactReflectedScalar2_grades (u a w : ℝ) :
    oddCompactReflectedScalar2 u a w =
      oddCompactReflectedScalar2Grade0 u a w +
      oddCompactReflectedScalar2Grade1 u a w +
      oddCompactReflectedScalar2Grade2 u a w +
      oddCompactReflectedScalar2Grade3 u a w +
      oddCompactReflectedScalar2Grade4 u a w +
      oddCompactReflectedScalar2Grade6 u a w := by
  unfold oddCompactReflectedScalar2 oddCompactReflectedScalar2Grade0 oddCompactReflectedScalar2Grade1 oddCompactReflectedScalar2Grade2 oddCompactReflectedScalar2Grade3 oddCompactReflectedScalar2Grade4 oddCompactReflectedScalar2Grade6
  ring

/-- Drift degree 0 of the reflected source scalar 4. -/
def oddCompactReflectedScalar4Grade0 (_u a w : ℝ) : ℝ :=
  ((48960 : ℝ) +
    (-80160 : ℝ)*a^(1 : ℕ) +
    (17844 : ℝ)*a^(2 : ℕ) +
    (48192 : ℝ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (308 : ℝ)*a^(3 : ℕ) +
    (-384 : ℝ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (27 : ℝ)*a^(4 : ℕ) +
    (-3072 : ℝ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (48 : ℝ)*a^(3 : ℕ)*w^(2 : ℕ)) / (4096 : ℝ)

/-- Drift degree 1 of the reflected source scalar 4. -/
def oddCompactReflectedScalar4Grade1 (u a w : ℝ) : ℝ :=
  ((-348 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-58 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (336 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (9 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (24 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ)) / (384 : ℝ)

/-- Drift degree 2 of the reflected source scalar 4. -/
def oddCompactReflectedScalar4Grade2 (u a w : ℝ) : ℝ :=
  ((-51840 : ℝ)*u^(2 : ℕ) +
    (37320 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ) +
    (-1930 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ) +
    (-15648 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (123 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ) +
    (-192 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (768 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ)) / (9216 : ℝ)

/-- Drift degree 3 of the reflected source scalar 4. -/
def oddCompactReflectedScalar4Grade3 (u a w : ℝ) : ℝ :=
  ((44 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (23 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-56 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ)) / (576 : ℝ)

/-- Drift degree 4 of the reflected source scalar 4. -/
def oddCompactReflectedScalar4Grade4 (u a w : ℝ) : ℝ :=
  ((27360 : ℝ)*u^(4 : ℕ) +
    (-7784 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ) +
    (319 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ) +
    (1200 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ)) / (27648 : ℝ)

/-- Drift degree 5 of the reflected source scalar 4. -/
def oddCompactReflectedScalar4Grade5 (u a w : ℝ) : ℝ :=
  ((7 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ)) / (2592 : ℝ)

/-- Drift degree 6 of the reflected source scalar 4. -/
def oddCompactReflectedScalar4Grade6 (u a _w : ℝ) : ℝ :=
  ((-2400 : ℝ)*u^(6 : ℕ) +
    (253 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ)) / (31104 : ℝ)

/-- Drift degree 8 of the reflected source scalar 4. -/
def oddCompactReflectedScalar4Grade8 (u _a _w : ℝ) : ℝ :=
  ((35 : ℝ)*u^(8 : ℕ)) / (15552 : ℝ)

/-- The reflected source scalar 4 is the sum of its drift grades. -/
theorem oddCompactReflectedScalar4_grades (u a w : ℝ) :
    oddCompactReflectedScalar4 u a w =
      oddCompactReflectedScalar4Grade0 u a w +
      oddCompactReflectedScalar4Grade1 u a w +
      oddCompactReflectedScalar4Grade2 u a w +
      oddCompactReflectedScalar4Grade3 u a w +
      oddCompactReflectedScalar4Grade4 u a w +
      oddCompactReflectedScalar4Grade5 u a w +
      oddCompactReflectedScalar4Grade6 u a w +
      oddCompactReflectedScalar4Grade8 u a w := by
  unfold oddCompactReflectedScalar4 oddCompactReflectedScalar4Grade0 oddCompactReflectedScalar4Grade1 oddCompactReflectedScalar4Grade2 oddCompactReflectedScalar4Grade3 oddCompactReflectedScalar4Grade4 oddCompactReflectedScalar4Grade5 oddCompactReflectedScalar4Grade6 oddCompactReflectedScalar4Grade8
  ring

/-- Drift degree 0 of the reflected source scalar 6. -/
def oddCompactReflectedScalar6Grade0 (_u a w : ℝ) : ℝ :=
  ((-6232320 : ℝ) +
    (15591360 : ℝ)*a^(1 : ℕ) +
    (-5340144 : ℝ)*a^(2 : ℕ) +
    (-14921472 : ℝ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-126076 : ℝ)*a^(3 : ℕ) +
    (288960 : ℝ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-32796 : ℝ)*a^(4 : ℕ) +
    (2012160 : ℝ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-38208 : ℝ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (21 : ℝ)*a^(5 : ℕ) +
    (24576 : ℝ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-816 : ℝ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-49152 : ℝ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (768 : ℝ)*a^(3 : ℕ)*w^(4 : ℕ)) / (16384 : ℝ)

/-- Drift degree 1 of the reflected source scalar 6. -/
def oddCompactReflectedScalar6Grade1 (u a w : ℝ) : ℝ :=
  ((93696 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-11384 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-421440 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-16902 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-41472 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-357 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (32256 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-1296 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (768 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ)) / (3072 : ℝ)

/-- Drift degree 2 of the reflected source scalar 6. -/
def oddCompactReflectedScalar6Grade2 (u a w : ℝ) : ℝ :=
  ((8907840 : ℝ)*u^(2 : ℕ) +
    (-10148160 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ) +
    (1366724 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ) +
    (6224448 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-175578 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ) +
    (-27744 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (1209 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ) +
    (-975360 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (720 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-44544 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (12288 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ)) / (36864 : ℝ)

/-- Drift degree 3 of the reflected source scalar 6. -/
def oddCompactReflectedScalar6Grade3 (u a w : ℝ) : ℝ :=
  ((32064 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-30968 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (82880 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-1247 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (4672 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-5376 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ)) / (4608 : ℝ)

/-- Drift degree 4 of the reflected source scalar 6. -/
def oddCompactReflectedScalar6Grade4 (u a w : ℝ) : ℝ :=
  ((-6698880 : ℝ)*u^(4 : ℕ) +
    (3859040 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ) +
    (-512732 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ) +
    (-792000 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (12435 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ) +
    (-48112 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (157440 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ)) / (110592 : ℝ)

/-- Drift degree 5 of the reflected source scalar 6. -/
def oddCompactReflectedScalar6Grade5 (u a w : ℝ) : ℝ :=
  ((-9376 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-1213 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-3160 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ)) / (10368 : ℝ)

/-- Drift degree 6 of the reflected source scalar 6. -/
def oddCompactReflectedScalar6Grade6 (u a w : ℝ) : ℝ :=
  ((1868640 : ℝ)*u^(6 : ℕ) +
    (-580656 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ) +
    (30865 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ) +
    (-9840 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ)) / (248832 : ℝ)

/-- Drift degree 7 of the reflected source scalar 6. -/
def oddCompactReflectedScalar6Grade7 (u a w : ℝ) : ℝ :=
  ((-53 : ℝ)*u^(7 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ)) / (1944 : ℝ)

/-- Drift degree 8 of the reflected source scalar 6. -/
def oddCompactReflectedScalar6Grade8 (u a _w : ℝ) : ℝ :=
  ((-258300 : ℝ)*u^(8 : ℕ) +
    (34189 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)) / (559872 : ℝ)

/-- Drift degree 10 of the reflected source scalar 6. -/
def oddCompactReflectedScalar6Grade10 (u _a _w : ℝ) : ℝ :=
  ((175 : ℝ)*u^(10 : ℕ)) / (15552 : ℝ)

/-- The reflected source scalar 6 is the sum of its drift grades. -/
theorem oddCompactReflectedScalar6_grades (u a w : ℝ) :
    oddCompactReflectedScalar6 u a w =
      oddCompactReflectedScalar6Grade0 u a w +
      oddCompactReflectedScalar6Grade1 u a w +
      oddCompactReflectedScalar6Grade2 u a w +
      oddCompactReflectedScalar6Grade3 u a w +
      oddCompactReflectedScalar6Grade4 u a w +
      oddCompactReflectedScalar6Grade5 u a w +
      oddCompactReflectedScalar6Grade6 u a w +
      oddCompactReflectedScalar6Grade7 u a w +
      oddCompactReflectedScalar6Grade8 u a w +
      oddCompactReflectedScalar6Grade10 u a w := by
  unfold oddCompactReflectedScalar6 oddCompactReflectedScalar6Grade0 oddCompactReflectedScalar6Grade1 oddCompactReflectedScalar6Grade2 oddCompactReflectedScalar6Grade3 oddCompactReflectedScalar6Grade4 oddCompactReflectedScalar6Grade5 oddCompactReflectedScalar6Grade6 oddCompactReflectedScalar6Grade7 oddCompactReflectedScalar6Grade8 oddCompactReflectedScalar6Grade10
  ring

/-- Drift degree 0 of the reflected source scalar 8. -/
def oddCompactReflectedScalar8Grade0 (_u a w : ℝ) : ℝ :=
  ((1236648960 : ℝ) +
    (-4346050560 : ℝ)*a^(1 : ℕ) +
    (2100223104 : ℝ)*a^(2 : ℕ) +
    (5924124672 : ℝ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (65544128 : ℝ)*a^(3 : ℕ) +
    (-196568064 : ℝ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (31855428 : ℝ)*a^(4 : ℕ) +
    (-1270628352 : ℝ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (28964736 : ℝ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-120108 : ℝ)*a^(5 : ℕ) +
    (-31927296 : ℝ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-1687296 : ℝ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (5133 : ℝ)*a^(6 : ℕ) +
    (65421312 : ℝ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-1956864 : ℝ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (83040 : ℝ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (1277952 : ℝ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (-26880 : ℝ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (-786432 : ℝ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (12288 : ℝ)*a^(3 : ℕ)*w^(6 : ℕ)) / (65536 : ℝ)

/-- Drift degree 1 of the reflected source scalar 8. -/
def oddCompactReflectedScalar8Grade1 (u a w : ℝ) : ℝ :=
  ((-2328384 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (6415936 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (64770048 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (3697020 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (8290560 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (373326 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-10635264 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (572112 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (1191 : ℝ)*u^(1 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (-581376 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (15048 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (264192 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (-10752 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (3072 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ)) / (3072 : ℝ)

/-- Drift degree 2 of the reflected source scalar 8. -/
def oddCompactReflectedScalar8Grade2 (u a w : ℝ) : ℝ :=
  ((-2304253440 : ℝ)*u^(2 : ℕ) +
    (3774059520 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ) +
    (-887253760 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ) +
    (-3107217408 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (179312976 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ) +
    (132786432 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-6497346 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ) +
    (942870528 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-40896 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-28485 : ℝ)*u^(2 : ℕ)*a^(5 : ℕ) +
    (82343424 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (412416 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-50601984 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (2913024 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-1474560 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (196608 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ)) / (147456 : ℝ)

/-- Drift degree 3 of the reflected source scalar 8. -/
def oddCompactReflectedScalar8Grade3 (u a w : ℝ) : ℝ :=
  ((-9900928 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (5223296 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-14743808 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (792260 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-1529088 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-3557 : ℝ)*u^(3 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (2928640 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-69688 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (167552 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (-44032 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ)) / (4608 : ℝ)

/-- Drift degree 4 of the reflected source scalar 8. -/
def oddCompactReflectedScalar8Grade4 (u a w : ℝ) : ℝ :=
  ((2320968960 : ℝ)*u^(4 : ℕ) +
    (-2186486784 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ) +
    (539612096 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ) +
    (516756480 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-41684688 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ) +
    (48247552 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-97413 : ℝ)*u^(4 : ℕ)*a^(4 : ℕ) +
    (-241192960 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (7570592 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-15202560 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (11415552 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ)) / (442368 : ℝ)

/-- Drift degree 5 of the reflected source scalar 8. -/
def oddCompactReflectedScalar8Grade5 (u a w : ℝ) : ℝ :=
  ((4812384 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (1401392 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (1092352 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-131959 : ℝ)*u^(5 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (361920 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-578048 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ)) / (20736 : ℝ)

/-- Drift degree 6 of the reflected source scalar 8. -/
def oddCompactReflectedScalar8Grade6 (u a w : ℝ) : ℝ :=
  ((-229022400 : ℝ)*u^(6 : ℕ) +
    (135786368 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ) +
    (-19424096 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ) +
    (1595648 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (230545 : ℝ)*u^(6 : ℕ)*a^(3 : ℕ) +
    (1519568 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (2049280 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ)) / (248832 : ℝ)

/-- Drift degree 7 of the reflected source scalar 8. -/
def oddCompactReflectedScalar8Grade7 (u a w : ℝ) : ℝ :=
  ((65458 : ℝ)*u^(7 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-28745 : ℝ)*u^(7 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (27564 : ℝ)*u^(7 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ)) / (5832 : ℝ)

/-- Drift degree 8 of the reflected source scalar 8. -/
def oddCompactReflectedScalar8Grade8 (u a w : ℝ) : ℝ :=
  ((100071720 : ℝ)*u^(8 : ℕ) +
    (-33767440 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ) +
    (1493319 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ) +
    (-7024 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ)) / (1119744 : ℝ)

/-- Drift degree 9 of the reflected source scalar 8. -/
def oddCompactReflectedScalar8Grade9 (u a w : ℝ) : ℝ :=
  ((-110159 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ)) / (104976 : ℝ)

/-- Drift degree 10 of the reflected source scalar 8. -/
def oddCompactReflectedScalar8Grade10 (u a _w : ℝ) : ℝ :=
  ((-319725 : ℝ)*u^(10 : ℕ) +
    (43102 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)) / (69984 : ℝ)

/-- Drift degree 12 of the reflected source scalar 8. -/
def oddCompactReflectedScalar8Grade12 (u _a _w : ℝ) : ℝ :=
  ((13475 : ℝ)*u^(12 : ℕ)) / (139968 : ℝ)

/-- The reflected source scalar 8 is the sum of its drift grades. -/
theorem oddCompactReflectedScalar8_grades (u a w : ℝ) :
    oddCompactReflectedScalar8 u a w =
      oddCompactReflectedScalar8Grade0 u a w +
      oddCompactReflectedScalar8Grade1 u a w +
      oddCompactReflectedScalar8Grade2 u a w +
      oddCompactReflectedScalar8Grade3 u a w +
      oddCompactReflectedScalar8Grade4 u a w +
      oddCompactReflectedScalar8Grade5 u a w +
      oddCompactReflectedScalar8Grade6 u a w +
      oddCompactReflectedScalar8Grade7 u a w +
      oddCompactReflectedScalar8Grade8 u a w +
      oddCompactReflectedScalar8Grade9 u a w +
      oddCompactReflectedScalar8Grade10 u a w +
      oddCompactReflectedScalar8Grade12 u a w := by
  unfold oddCompactReflectedScalar8 oddCompactReflectedScalar8Grade0 oddCompactReflectedScalar8Grade1 oddCompactReflectedScalar8Grade2 oddCompactReflectedScalar8Grade3 oddCompactReflectedScalar8Grade4 oddCompactReflectedScalar8Grade5 oddCompactReflectedScalar8Grade6 oddCompactReflectedScalar8Grade7 oddCompactReflectedScalar8Grade8 oddCompactReflectedScalar8Grade9 oddCompactReflectedScalar8Grade10 oddCompactReflectedScalar8Grade12
  ring

/-- Drift degree 0 of the reflected source scalar 10. -/
def oddCompactReflectedScalar10Grade0 (_u a w : ℝ) : ℝ :=
  ((-348431339520 : ℝ) +
    (1630027637760 : ℝ)*a^(1 : ℕ) +
    (-1049498863104 : ℝ)*a^(2 : ℕ) +
    (-2968556593152 : ℝ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-41941787776 : ℝ)*a^(3 : ℕ) +
    (145697617920 : ℝ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-31469666832 : ℝ)*a^(4 : ℕ) +
    (899693445120 : ℝ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-24323329536 : ℝ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (249467508 : ℝ)*a^(5 : ℕ) +
    (35124129792 : ℝ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (5286870144 : ℝ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-12875940 : ℝ)*a^(6 : ℕ) +
    (-73162358784 : ℝ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (3323464704 : ℝ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-363526848 : ℝ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (725859 : ℝ)*a^(7 : ℕ) +
    (-2978758656 : ℝ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (-694342656 : ℝ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (1213344 : ℝ)*a^(6 : ℕ)*w^(2 : ℕ) +
    (1842610176 : ℝ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (-87048192 : ℝ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (8903424 : ℝ)*a^(5 : ℕ)*w^(4 : ℕ) +
    (40894464 : ℝ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (-749568 : ℝ)*a^(4 : ℕ)*w^(6 : ℕ) +
    (-12582912 : ℝ)*a^(1 : ℕ)*w^(10 : ℕ) +
    (196608 : ℝ)*a^(3 : ℕ)*w^(8 : ℕ)) / (262144 : ℝ)

/-- Drift degree 1 of the reflected source scalar 10. -/
def oddCompactReflectedScalar10Grade1 (u a w : ℝ) : ℝ :=
  ((-4242353664 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-24675282944 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-180189972480 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-13883203584 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-28908570624 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-2936028240 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (47284273152 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-3244053888 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (5008590 : ℝ)*u^(1 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (4182349824 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (111678336 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (650637 : ℝ)*u^(1 : ℕ)*a^(6 : ℕ)*w^(1 : ℕ) +
    (-2468265984 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (182564352 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (-43680 : ℝ)*u^(1 : ℕ)*a^(5 : ℕ)*w^(3 : ℕ) +
    (-104300544 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (2767104 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(5 : ℕ) +
    (28704768 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(9 : ℕ) +
    (-1191936 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(7 : ℕ) +
    (196608 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(9 : ℕ)) / (49152 : ℝ)

/-- Drift degree 2 of the reflected source scalar 10. -/
def oddCompactReflectedScalar10Grade2 (u a w : ℝ) : ℝ :=
  ((823023037440 : ℝ)*u^(2 : ℕ) +
    (-1820056604160 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ) +
    (637387274624 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ) +
    (1917267253248 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-181124155776 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ) +
    (-186928232448 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (13346355564 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ) +
    (-921561169920 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-1847221632 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (41297310 : ℝ)*u^(2 : ℕ)*a^(5 : ℕ) +
    (-120089207808 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-5074187328 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (3330819 : ℝ)*u^(2 : ℕ)*a^(6 : ℕ) +
    (98214395904 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (-9388076544 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-12892752 : ℝ)*u^(2 : ℕ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (6689267712 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (-26691840 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ)*w^(4 : ℕ) +
    (-2133983232 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (138498048 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(6 : ℕ) +
    (-40501248 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(8 : ℕ) +
    (3145728 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(10 : ℕ)) / (589824 : ℝ)

/-- Drift degree 3 of the reflected source scalar 10. -/
def oddCompactReflectedScalar10Grade3 (u a w : ℝ) : ℝ :=
  ((34952859904 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-16117062656 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (46932930560 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-5384779008 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (6652007424 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (293244528 : ℝ)*u^(3 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (-18642100224 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (826916992 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (5207539 : ℝ)*u^(3 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (-2190985216 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (-6954944 : ℝ)*u^(3 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    (904151040 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    (-74385664 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (32538624 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (-4784128 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(9 : ℕ)) / (73728 : ℝ)

/-- Drift degree 4 of the reflected source scalar 10. -/
def oddCompactReflectedScalar10Grade4 (u a w : ℝ) : ℝ :=
  ((-1065190394880 : ℝ)*u^(4 : ℕ) +
    (1462980547840 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ) +
    (-551799974144 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ) +
    (-383495884800 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (77777866944 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ) +
    (-35336745984 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-1031344836 : ℝ)*u^(4 : ℕ)*a^(4 : ℕ) +
    (308949565440 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (-26256941952 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (596311 : ℝ)*u^(4 : ℕ)*a^(5 : ℕ) +
    (39930997760 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (188098656 : ℝ)*u^(4 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-39897022464 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    (2276129024 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (-2386800640 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (557776896 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ)) / (1769472 : ℝ)

/-- Drift degree 5 of the reflected source scalar 10. -/
def oddCompactReflectedScalar10Grade5 (u a w : ℝ) : ℝ :=
  ((-4918674496 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-2266144512 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-2125056 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (575695968 : ℝ)*u^(5 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-810858624 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (6532665 : ℝ)*u^(5 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    (1551633408 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ) +
    (-88052040 : ℝ)*u^(5 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    (129646720 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    (-61596672 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ)) / (82944 : ℝ)

/-- Drift degree 6 of the reflected source scalar 10. -/
def oddCompactReflectedScalar10Grade6 (u a w : ℝ) : ℝ :=
  ((557208464640 : ℝ)*u^(6 : ℕ) +
    (-523135505152 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ) +
    (132142454592 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ) +
    (1554207744 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-6335779744 : ℝ)*u^(6 : ℕ)*a^(3 : ℕ) +
    (-22289547776 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-3752845 : ℝ)*u^(6 : ℕ)*a^(4 : ℕ) +
    (-13501636608 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (2400080800 : ℝ)*u^(6 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-3109978368 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (3313938432 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ)) / (3981312 : ℝ)

/-- Drift degree 7 of the reflected source scalar 10. -/
def oddCompactReflectedScalar10Grade7 (u a w : ℝ) : ℝ :=
  ((-43222479 : ℝ)*u^(7 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (44135618 : ℝ)*u^(7 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-42046728 : ℝ)*u^(7 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-704815 : ℝ)*u^(7 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-1186402 : ℝ)*u^(7 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-3225936 : ℝ)*u^(7 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ)) / (11664 : ℝ)

/-- Drift degree 8 of the reflected source scalar 10. -/
def oddCompactReflectedScalar10Grade8 (u a w : ℝ) : ℝ :=
  ((-85437424800 : ℝ)*u^(8 : ℕ) +
    (51347405928 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ) +
    (-6108485748 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ) +
    (-2112851520 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (69149685 : ℝ)*u^(8 : ℕ)*a^(3 : ℕ) +
    (1499492432 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-710325504 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ)) / (4478976 : ℝ)

/-- Drift degree 9 of the reflected source scalar 10. -/
def oddCompactReflectedScalar10Grade9 (u a w : ℝ) : ℝ :=
  ((141032879 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-16346760 : ℝ)*u^(9 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (18139284 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ)) / (209952 : ℝ)

/-- Drift degree 10 of the reflected source scalar 10. -/
def oddCompactReflectedScalar10Grade10 (u a w : ℝ) : ℝ :=
  ((15433853400 : ℝ)*u^(10 : ℕ) +
    (-5018265844 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ) +
    (200330885 : ℝ)*u^(10 : ℕ)*a^(2 : ℕ) +
    (415476048 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ)) / (10077696 : ℝ)

/-- Drift degree 11 of the reflected source scalar 10. -/
def oddCompactReflectedScalar10Grade11 (u a w : ℝ) : ℝ :=
  ((-34652003 : ℝ)*u^(11 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ)) / (1889568 : ℝ)

/-- Drift degree 12 of the reflected source scalar 10. -/
def oddCompactReflectedScalar10Grade12 (u a _w : ℝ) : ℝ :=
  ((-3051764100 : ℝ)*u^(12 : ℕ) +
    (389189099 : ℝ)*u^(12 : ℕ)*a^(1 : ℕ)) / (45349632 : ℝ)

/-- Drift degree 14 of the reflected source scalar 10. -/
def oddCompactReflectedScalar10Grade14 (u _a _w : ℝ) : ℝ :=
  ((175175 : ℝ)*u^(14 : ℕ)) / (139968 : ℝ)

/-- The reflected source scalar 10 is the sum of its drift grades. -/
theorem oddCompactReflectedScalar10_grades (u a w : ℝ) :
    oddCompactReflectedScalar10 u a w =
      oddCompactReflectedScalar10Grade0 u a w +
      oddCompactReflectedScalar10Grade1 u a w +
      oddCompactReflectedScalar10Grade2 u a w +
      oddCompactReflectedScalar10Grade3 u a w +
      oddCompactReflectedScalar10Grade4 u a w +
      oddCompactReflectedScalar10Grade5 u a w +
      oddCompactReflectedScalar10Grade6 u a w +
      oddCompactReflectedScalar10Grade7 u a w +
      oddCompactReflectedScalar10Grade8 u a w +
      oddCompactReflectedScalar10Grade9 u a w +
      oddCompactReflectedScalar10Grade10 u a w +
      oddCompactReflectedScalar10Grade11 u a w +
      oddCompactReflectedScalar10Grade12 u a w +
      oddCompactReflectedScalar10Grade14 u a w := by
  unfold oddCompactReflectedScalar10 oddCompactReflectedScalar10Grade0 oddCompactReflectedScalar10Grade1 oddCompactReflectedScalar10Grade2 oddCompactReflectedScalar10Grade3 oddCompactReflectedScalar10Grade4 oddCompactReflectedScalar10Grade5 oddCompactReflectedScalar10Grade6 oddCompactReflectedScalar10Grade7 oddCompactReflectedScalar10Grade8 oddCompactReflectedScalar10Grade9 oddCompactReflectedScalar10Grade10 oddCompactReflectedScalar10Grade11 oddCompactReflectedScalar10Grade12 oddCompactReflectedScalar10Grade14
  ring

end
end HTGeometry
