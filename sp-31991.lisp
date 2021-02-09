(declaim (optimize speed))

;;; This is a dump of (macroexpand (def-sp-p 31991)).

(PROGN (DEFSTRUCT (SP-31991 (:CONSTRUCTOR MAKE-SP-31991-PRIVATE))
         "Type of a sparse-elt over F_31991, the field of thirty-one thousand nine hundred ninety-one elements."
         SHEAFHOM2::I
         SHEAFHOM2::V)
       (DEFMETHOD MAKE-SP-31991 ((SHEAFHOM2::INDEX FIXNUM)
                                 (SHEAFHOM2::VALUE INTEGER))
         "Creates a sparse-elt over F_31991, the field of thirty-one thousand nine hundred ninety-one elements."
         (MAKE-SP-31991-PRIVATE :I SHEAFHOM2::INDEX :V
          (MOD (THE INTEGER SHEAFHOM2::VALUE) 31991)))
       (EXPORT (LIST 'SP-31991 'MAKE-SP-31991))
       (DEFMETHOD COPY-SP ((ELT SP-31991) SHEAFHOM2::NEW-INDEX)
         (MAKE-SP-31991-PRIVATE :I
          (OR SHEAFHOM2::NEW-INDEX (SP-31991-I ELT)) :V
          (SP-31991-V ELT)))
       (DEFMETHOD SP-PRINT-VALUE ((ELT SP-31991) &OPTIONAL STREAM)
         (FORMAT STREAM "~D" (THE (MOD 31991) (SP-31991-V ELT))))
       (DEFMETHOD SP-I-FUNC ((ELT SP-31991)) (SP-31991-I ELT))
       (DEFMETHOD SP-ZEROP ((ELT SP-31991))
         (ZEROP (THE (MOD 31991) (SP-31991-V ELT))))
       (DEFMETHOD SP-ONEP ((ELT SP-31991))
         (= 1 (THE (MOD 31991) (SP-31991-V ELT))))
       (DEFMETHOD SP-NEG-ONE-P ((ELT SP-31991))
         (= 31990 (THE (MOD 31991) (SP-31991-V ELT))))
       (DEFMETHOD SP-UNITP ((ELT SP-31991))
         (NOT (ZEROP (THE (MOD 31991) (SP-31991-V ELT)))))
       (DEFMETHOD SP-ADD ((SHEAFHOM2::X SP-31991)
                          (SHEAFHOM2::Y SP-31991) &OPTIONAL
                          SHEAFHOM2::NEW-INDEX)
         (MAKE-SP-31991-PRIVATE :I
          (OR SHEAFHOM2::NEW-INDEX (SP-31991-I SHEAFHOM2::X)) :V
          (MOD (THE (INTEGER 0 63980)
                    (+ (THE (MOD 31991) (SP-31991-V SHEAFHOM2::X))
                       (THE (MOD 31991) (SP-31991-V SHEAFHOM2::Y))))
               31991)))
       (DEFMETHOD SP-SUBTRACT ((SHEAFHOM2::X SP-31991)
                               (SHEAFHOM2::Y SP-31991) &OPTIONAL
                               SHEAFHOM2::NEW-INDEX)
         (MAKE-SP-31991-PRIVATE :I
          (OR SHEAFHOM2::NEW-INDEX (SP-31991-I SHEAFHOM2::X)) :V
          (MOD (THE (INTEGER -31990 31990)
                    (- (THE (MOD 31991) (SP-31991-V SHEAFHOM2::X))
                       (THE (MOD 31991) (SP-31991-V SHEAFHOM2::Y))))
               31991)))
       (DEFMETHOD SP-NEGATE ((ELT SP-31991) &OPTIONAL
                             SHEAFHOM2::NEW-INDEX)
         (MAKE-SP-31991-PRIVATE :I
          (OR SHEAFHOM2::NEW-INDEX (SP-31991-I ELT)) :V
          (MOD (THE (INTEGER -31990 0)
                    (- (THE (MOD 31991) (SP-31991-V ELT))))
               31991)))
       (DEFMETHOD SP-MULT ((SHEAFHOM2::X SP-31991)
                           (SHEAFHOM2::Y SP-31991) &OPTIONAL
                           SHEAFHOM2::NEW-INDEX)
         (MAKE-SP-31991-PRIVATE :I
          (OR SHEAFHOM2::NEW-INDEX (SP-31991-I SHEAFHOM2::X)) :V
          (MOD (THE (INTEGER 0 1023360100)
                    (* (THE (MOD 31991) (SP-31991-V SHEAFHOM2::X))
                       (THE (MOD 31991) (SP-31991-V SHEAFHOM2::Y))))
               31991)))
       (DEFMETHOD SP-DIVIDES ((SHEAFHOM2::X SP-31991)
                              (SHEAFHOM2::Y SP-31991))
         T)
       (DEFMETHOD SP-DIVIDED-BY ((SHEAFHOM2::X SP-31991)
                                 (SHEAFHOM2::Y SP-31991)
                                 &OPTIONAL
                                 SHEAFHOM2::NEW-INDEX)
         (MULTIPLE-VALUE-BIND (SHEAFHOM2::U SHEAFHOM2::V SHEAFHOM2::D)
             (EXT-GCD (THE (MOD 31991) (SP-31991-V SHEAFHOM2::Y))
                      31991)
           (DECLARE (INTEGER SHEAFHOM2::U) (IGNORE SHEAFHOM2::V)
                    (TYPE (INTEGER 0 *) SHEAFHOM2::D))
           (ASSERT (= SHEAFHOM2::D 1) NIL "Can't invert ~D mod ~D."
                   (SP-31991-V SHEAFHOM2::Y) 31991)
           (MAKE-SP-31991-PRIVATE :I
            (OR SHEAFHOM2::NEW-INDEX (SP-31991-I SHEAFHOM2::X)) :V
            (MOD (THE INTEGER
                      (* (THE (MOD 31991) (SP-31991-V SHEAFHOM2::X))
                         SHEAFHOM2::U))
                 31991))))
       (DEFMETHOD SP-PRETTY-ASSOCIATE ((SHEAFHOM2::ELT SP-31991))
	 (IF (SP-ZEROP SHEAFHOM2::ELT)
	     (VALUES SHEAFHOM2::ELT (SP-EMBED-Z SHEAFHOM2::ELT 1))
	   (VALUES (SP-EMBED-Z SHEAFHOM2::ELT 1) SHEAFHOM2::ELT)))
       (DEFMETHOD SP-= ((SHEAFHOM2::X SP-31991)
                        (SHEAFHOM2::Y SP-31991))
         (= (THE (MOD 31991) (SP-31991-V SHEAFHOM2::X))
            (THE (MOD 31991) (SP-31991-V SHEAFHOM2::Y))))
       (DEFMETHOD SP-EMBED-Z ((SHEAFHOM2::SAMPLE-ELT SP-31991)
                              (SHEAFHOM2::VALUE INTEGER) &OPTIONAL
                              SHEAFHOM2::NEW-INDEX)
         (MAKE-SP-31991-PRIVATE :I
          (OR SHEAFHOM2::NEW-INDEX (SP-31991-I SHEAFHOM2::SAMPLE-ELT))
          :V (MOD (THE INTEGER SHEAFHOM2::VALUE) 31991)))
       (DEFMETHOD SP-RING-NAME ((ELT SP-31991)) "F_31991")
       (DEFMETHOD SP-EUC-NORM ((ELT SP-31991))
         (IF (ZEROP (THE (MOD 31991) (SP-31991-V ELT))) 0 1))
       (DEFMETHOD SP-NEG-CLOSEST-QUOTIENT ((SHEAFHOM2::X SP-31991)
                                           (SHEAFHOM2::Y SP-31991)
                                           &OPTIONAL
                                           SHEAFHOM2::NEW-INDEX)
         (MULTIPLE-VALUE-BIND (SHEAFHOM2::U SHEAFHOM2::V SHEAFHOM2::D)
             (EXT-GCD (THE (MOD 31991) (SP-31991-V SHEAFHOM2::Y))
                      31991)
           (DECLARE (INTEGER SHEAFHOM2::U) (IGNORE SHEAFHOM2::V)
                    (TYPE (INTEGER 0 *) SHEAFHOM2::D))
           (ASSERT (= SHEAFHOM2::D 1) NIL "Can't invert ~D mod ~D."
                   (SP-31991-V SHEAFHOM2::Y) 31991)
           (MAKE-SP-31991-PRIVATE :I
            (OR SHEAFHOM2::NEW-INDEX (SP-31991-I SHEAFHOM2::X)) :V
            (MOD (THE INTEGER
                      (* -1 (THE (MOD 31991) (SP-31991-V SHEAFHOM2::X))
                         SHEAFHOM2::U))
                 31991))))
       (DEFMETHOD SP-ROUNDED-REM ((SHEAFHOM2::X SP-31991)
                                  (SHEAFHOM2::Y SP-31991)
                                  &OPTIONAL
                                  SHEAFHOM2::NEW-INDEX)
         "As the defgeneric says, it is an error if y is zero.~&This method doesn't signal the error."
         (MAKE-SP-31991-PRIVATE :I
          (OR SHEAFHOM2::NEW-INDEX (SP-31991-I SHEAFHOM2::X)) :V 0))
       (DEFMETHOD SP-INTEGRITY-CHECK ((ELT SP-31991) &KEY (MESSAGE ""))
	 (LET ((V (SP-31991-V ELT)))
	   (ASSERT (AND (<= 0 V) (< V 31991)) ()
	     "~AValue ~A out of range [0,~D) for ~A." MESSAGE V 31991 SP-31991)))
       (DEFMETHOD SP-INTEGER-LIFT ((ELT SP-31991))
         (SP-31991-V ELT))
       (DEFMETHOD SP-FIELD-P ((ELT SP-31991))
	 T)
       (DEFMETHOD SP-F_P-P ((ELT SP-31991))
	 31991)
       NIL)