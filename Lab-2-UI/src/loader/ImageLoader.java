package loader;

import javafx.scene.image.Image;

import java.io.FileNotFoundException;
import java.io.InputStream;
import java.util.logging.Logger;

/**
 * Created by halitanil on 08.02.2014.
 */
public class ImageLoader {

    /**
     * Attempts to load an image for the resource image directory.
     *
     * @param fileName Name of the image to load
     * @return The image with associated name.
     * @throws java.io.FileNotFoundException Unable to find fileName
     */
    public static Image load(String fileName) throws FileNotFoundException {
        InputStream stream = ImageLoader.class.
                getClassLoader().getResourceAsStream("images/" + fileName);
        if (stream == null) {
            Logger.getGlobal().warning("Unable to find image " + fileName);
            throw new FileNotFoundException("Unable to find image " + fileName);
        }
        return new Image(stream);
    }
}
