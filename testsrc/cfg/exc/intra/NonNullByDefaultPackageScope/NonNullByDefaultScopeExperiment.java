package cfg.exc.intra.NonNullByDefaultPackageScope;

import org.eclipse.jdt.annotation.DefaultLocation;
import org.eclipse.jdt.annotation.NonNull;
import org.eclipse.jdt.annotation.NonNullByDefault;
import org.eclipse.jdt.annotation.Nullable;

@NonNullByDefault({DefaultLocation.FIELD})
public class NonNullByDefaultScopeExperiment {
  static class Outer {
    @NonNullByDefault({DefaultLocation.PARAMETER})
    Object z = new Innter () {
      @SuppressWarnings("unused")
      void lol(Object a, @Nullable Object b) {
        @NonNull Object x = a;
        @NonNull Object y = b;
        
        x.toString();
        y.toString();
      }
    };
    
    static class Innter {
      static void foo(Object a, @Nullable Object b) {
        @NonNull Object x = a;
        @NonNull Object y = b;
        
        Object z = new Cloneable() {
          @SuppressWarnings("unused")
          void bar(Object a, @Nullable Object b) {
            @NonNull Object x = a;
            @NonNull Object y = b;
            
            x.toString();
            y.toString();
          }
        };

        x.toString();
        y.toString();
        
        z.toString();
      }
    }
  }
}
